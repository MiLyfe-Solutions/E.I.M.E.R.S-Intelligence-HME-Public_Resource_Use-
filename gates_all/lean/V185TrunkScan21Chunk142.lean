import V185TrunkScan21Chunk141

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1731441 : List Nat := [1, 2, 2, 2, 1, 6, 2, 5]
def baseStart_1731441 : Nat := 118140960795 + 1731441 * 2 ^ 59
def prefixEnd_1731441 : Nat := 4983230072969 + 3 ^ 40 * 1731441 * 2
def baseEnd_1731441 : Nat := 131712808577994883381445

theorem tailTrace_1731441 : CollatzResearch.WordTrace tailWord_1731441 prefixEnd_1731441 131712808577994883381445 := by
  unfold tailWord_1731441
  simp only [CollatzResearch.WordTrace]
  refine ⟨63150841320292438425506177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42100560880194958950337451 63150841320292438425506177)
  ·
    refine ⟨47363130990219328819129633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63150841320292438425506177 47363130990219328819129633)
    ·
      refine ⟨35522348242664496614347225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47363130990219328819129633 35522348242664496614347225)
      ·
        refine ⟨26641761181998372460760419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35522348242664496614347225 26641761181998372460760419)
        ·
          refine ⟨39962641772997558691140629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26641761181998372460760419 39962641772997558691140629)
          ·
            refine ⟨1873248833109260563647217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39962641772997558691140629 1873248833109260563647217)
            ·
              refine ⟨1404936624831945422735413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873248833109260563647217 1404936624831945422735413)
              ·
                refine ⟨131712808577994883381445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1404936624831945422735413 131712808577994883381445)
                ·
                  rfl

theorem cell21_1731441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 5].length) (baseStart_1731441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731441 prefixEnd_1731441 := by exact prefixLift 1731441
  have htrace : WordTrace (prefixWord ++ tailWord_1731441) baseStart_1731441 baseEnd_1731441 := by
    simpa [prefixWord, tailWord_1731441, baseEnd_1731441] using wordTrace_append hprefix tailTrace_1731441
  have hstable : (prefixWord ++ tailWord_1731441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731441).length < 2 ^ (prefixWord ++ tailWord_1731441).sum := by decide
  have hdescent : baseEnd_1731441 < baseStart_1731441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731478 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1731478 : Nat := 118140960795 + 1731478 * 2 ^ 59
def prefixEnd_1731478 : Nat := 4983230072969 + 3 ^ 40 * 1731478 * 2
def baseEnd_1731478 : Nat := 395146869638080808027593

theorem tailTrace_1731478 : CollatzResearch.WordTrace tailWord_1731478 prefixEnd_1731478 395146869638080808027593 := by
  unfold tailWord_1731478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947011926322399609037693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42101460547438929163068725 3947011926322399609037693)
  ·
    refine ⟨1480129472370899853389135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3947011926322399609037693 1480129472370899853389135)
    ·
      refine ⟨2220194208556349780083703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1480129472370899853389135 2220194208556349780083703)
      ·
        refine ⟨3330291312834524670125555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220194208556349780083703 3330291312834524670125555)
        ·
          refine ⟨4995436969251787005188333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3330291312834524670125555 4995436969251787005188333)
          ·
            refine ⟨1873288863469420126945625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4995436969251787005188333 1873288863469420126945625)
            ·
              refine ⟨1404966647602065095209219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873288863469420126945625 1404966647602065095209219)
              ·
                refine ⟨2107449971403097642813829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404966647602065095209219 2107449971403097642813829)
                ·
                  refine ⟨395146869638080808027593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2107449971403097642813829 395146869638080808027593)
                  ·
                    rfl

theorem cell21_1731478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1731478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731478 prefixEnd_1731478 := by exact prefixLift 1731478
  have htrace : WordTrace (prefixWord ++ tailWord_1731478) baseStart_1731478 baseEnd_1731478 := by
    simpa [prefixWord, tailWord_1731478, baseEnd_1731478] using wordTrace_append hprefix tailTrace_1731478
  have hstable : (prefixWord ++ tailWord_1731478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731478).length < 2 ^ (prefixWord ++ tailWord_1731478).sum := by decide
  have hdescent : baseEnd_1731478 < baseStart_1731478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731607 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 5]
def baseStart_1731607 : Nat := 118140960795 + 1731607 * 2 ^ 59
def prefixEnd_1731607 : Nat := 4983230072969 + 3 ^ 40 * 1731607 * 2
def baseEnd_1731607 : Nat := 395176309195605250377329

theorem tailTrace_1731607 : CollatzResearch.WordTrace tailWord_1731607 prefixEnd_1731607 395176309195605250377329 := by
  unfold tailWord_1731607
  simp only [CollatzResearch.WordTrace]
  refine ⟨63156895837691048776049075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42104597225127365850699383 63156895837691048776049075)
  ·
    refine ⟨94735343756536573164073613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63156895837691048776049075 94735343756536573164073613)
    ·
      refine ⟨35525753908701214936527605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94735343756536573164073613 35525753908701214936527605)
      ·
        refine ⟨3330539428940738900299463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35525753908701214936527605 3330539428940738900299463)
        ·
          refine ⟨4995809143411108350449195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3330539428940738900299463 4995809143411108350449195)
          ·
            refine ⟨7493713715116662525673793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995809143411108350449195 7493713715116662525673793)
            ·
              refine ⟨5620285286337496894255345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7493713715116662525673793 5620285286337496894255345)
              ·
                refine ⟨4215213964753122670691509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620285286337496894255345 4215213964753122670691509)
                ·
                  refine ⟨395176309195605250377329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4215213964753122670691509 395176309195605250377329)
                  ·
                    rfl

theorem cell21_1731607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_1731607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731607 prefixEnd_1731607 := by exact prefixLift 1731607
  have htrace : WordTrace (prefixWord ++ tailWord_1731607) baseStart_1731607 baseEnd_1731607 := by
    simpa [prefixWord, tailWord_1731607, baseEnd_1731607] using wordTrace_append hprefix tailTrace_1731607
  have hstable : (prefixWord ++ tailWord_1731607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731607).length < 2 ^ (prefixWord ++ tailWord_1731607).sum := by decide
  have hdescent : baseEnd_1731607 < baseStart_1731607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731638 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1731638 : Nat := 118140960795 + 1731638 * 2 ^ 59
def prefixEnd_1731638 : Nat := 4983230072969 + 3 ^ 40 * 1731638 * 2
def baseEnd_1731638 : Nat := 395183383817956085360599

theorem tailTrace_1731638 : CollatzResearch.WordTrace tailWord_1731638 prefixEnd_1731638 395183383817956085360599 := by
  unfold tailWord_1731638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947376656286171316901723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42105351000385827380285045 3947376656286171316901723)
  ·
    refine ⟨5921064984429256975352585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3947376656286171316901723 5921064984429256975352585)
    ·
      refine ⟨4440798738321942731514439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5921064984429256975352585 4440798738321942731514439)
      ·
        refine ⟨6661198107482914097271659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440798738321942731514439 6661198107482914097271659)
        ·
          refine ⟨9991797161224371145907489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661198107482914097271659 9991797161224371145907489)
          ·
            refine ⟨7493847870918278359430617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9991797161224371145907489 7493847870918278359430617)
            ·
              refine ⟨5620385903188708769572963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7493847870918278359430617 5620385903188708769572963)
              ·
                refine ⟨8430578854783063154359445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620385903188708769572963 8430578854783063154359445)
                ·
                  refine ⟨395183383817956085360599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8430578854783063154359445 395183383817956085360599)
                  ·
                    rfl

theorem cell21_1731638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1731638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731638 prefixEnd_1731638 := by exact prefixLift 1731638
  have htrace : WordTrace (prefixWord ++ tailWord_1731638) baseStart_1731638 baseEnd_1731638 := by
    simpa [prefixWord, tailWord_1731638, baseEnd_1731638] using wordTrace_append hprefix tailTrace_1731638
  have hstable : (prefixWord ++ tailWord_1731638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731638).length < 2 ^ (prefixWord ++ tailWord_1731638).sum := by decide
  have hdescent : baseEnd_1731638 < baseStart_1731638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731641 : List Nat := [1, 2, 1, 5, 2, 2, 3, 2, 3]
def baseStart_1731641 : Nat := 118140960795 + 1731641 * 2 ^ 59
def prefixEnd_1731641 : Nat := 4983230072969 + 3 ^ 40 * 1731641 * 2
def baseEnd_1731641 : Nat := 395184068458828746810593

theorem tailTrace_1731641 : CollatzResearch.WordTrace tailWord_1731641 prefixEnd_1731641 395184068458828746810593 := by
  unfold tailWord_1731641
  simp only [CollatzResearch.WordTrace]
  refine ⟨63158135919567872582786777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42105423946378581721857851 63158135919567872582786777)
  ·
    refine ⟨47368601939675904437090083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63158135919567872582786777 47368601939675904437090083)
    ·
      refine ⟨71052902909513856655635125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47368601939675904437090083 71052902909513856655635125)
      ·
        refine ⟨6661209647766924061465793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71052902909513856655635125 6661209647766924061465793)
        ·
          refine ⟨4995907235825193046099345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6661209647766924061465793 4995907235825193046099345)
          ·
            refine ⟨3746930426868894784574509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4995907235825193046099345 3746930426868894784574509)
            ·
              refine ⟨1405098910075835544215441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3746930426868894784574509 1405098910075835544215441)
              ·
                refine ⟨1053824182556876658161581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405098910075835544215441 1053824182556876658161581)
                ·
                  refine ⟨395184068458828746810593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053824182556876658161581 395184068458828746810593)
                  ·
                    rfl

theorem cell21_1731641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_1731641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731641 prefixEnd_1731641 := by exact prefixLift 1731641
  have htrace : WordTrace (prefixWord ++ tailWord_1731641) baseStart_1731641 baseEnd_1731641 := by
    simpa [prefixWord, tailWord_1731641, baseEnd_1731641] using wordTrace_append hprefix tailTrace_1731641
  have hstable : (prefixWord ++ tailWord_1731641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731641).length < 2 ^ (prefixWord ++ tailWord_1731641).sum := by decide
  have hdescent : baseEnd_1731641 < baseStart_1731641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731655 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 4]
def baseStart_1731655 : Nat := 118140960795 + 1731655 * 2 ^ 59
def prefixEnd_1731655 : Nat := 4983230072969 + 3 ^ 40 * 1731655 * 2
def baseEnd_1731655 : Nat := 395187263449567833577231

theorem tailTrace_1731655 : CollatzResearch.WordTrace tailWord_1731655 prefixEnd_1731655 395187263449567833577231 := by
  unfold tailWord_1731655
  simp only [CollatzResearch.WordTrace]
  refine ⟨63158646541517152973796419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42105764361011435315864279 63158646541517152973796419)
  ·
    refine ⟨94737969812275729460694629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63158646541517152973796419 94737969812275729460694629)
    ·
      refine ⟨17763369339801699273880243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94737969812275729460694629 17763369339801699273880243)
      ·
        refine ⟨26645054009702548910820365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17763369339801699273880243 26645054009702548910820365)
        ·
          refine ⟨9991895253638455841557637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26645054009702548910820365 9991895253638455841557637)
          ·
            refine ⟨1873480360057210470292057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9991895253638455841557637 1873480360057210470292057)
            ·
              refine ⟨1405110270042907852719043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873480360057210470292057 1405110270042907852719043)
              ·
                refine ⟨2107665405064361779078565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405110270042907852719043 2107665405064361779078565)
                ·
                  refine ⟨395187263449567833577231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2107665405064361779078565 395187263449567833577231)
                  ·
                    rfl

theorem cell21_1731655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 4].length) (baseStart_1731655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731655 prefixEnd_1731655 := by exact prefixLift 1731655
  have htrace : WordTrace (prefixWord ++ tailWord_1731655) baseStart_1731655 baseEnd_1731655 := by
    simpa [prefixWord, tailWord_1731655, baseEnd_1731655] using wordTrace_append hprefix tailTrace_1731655
  have hstable : (prefixWord ++ tailWord_1731655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731655).length < 2 ^ (prefixWord ++ tailWord_1731655).sum := by decide
  have hdescent : baseEnd_1731655 < baseStart_1731655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731683 : List Nat := [1, 1, 1, 5, 1, 1, 1, 7, 3]
def baseStart_1731683 : Nat := 118140960795 + 1731683 * 2 ^ 59
def prefixEnd_1731683 : Nat := 4983230072969 + 3 ^ 40 * 1731683 * 2
def baseEnd_1731683 : Nat := 395193653431046007110507

theorem tailTrace_1731683 : CollatzResearch.WordTrace tailWord_1731683 prefixEnd_1731683 395193653431046007110507 := by
  unfold tailWord_1731683
  simp only [CollatzResearch.WordTrace]
  refine ⟨63159667785415713755815703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42106445190277142503877135 63159667785415713755815703)
  ·
    refine ⟨94739501678123570633723555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63159667785415713755815703 94739501678123570633723555)
    ·
      refine ⟨142109252517185355950585333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94739501678123570633723555 142109252517185355950585333)
      ·
        refine ⟨13322742423486127120367375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142109252517185355950585333 13322742423486127120367375)
        ·
          refine ⟨19984113635229190680551063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13322742423486127120367375 19984113635229190680551063)
          ·
            refine ⟨29976170452843786020826595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19984113635229190680551063 29976170452843786020826595)
            ·
              refine ⟨44964255679265679031239893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29976170452843786020826595 44964255679265679031239893)
              ·
                refine ⟨1053849742482789352294685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44964255679265679031239893 1053849742482789352294685)
                ·
                  refine ⟨395193653431046007110507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053849742482789352294685 395193653431046007110507)
                  ·
                    rfl

theorem cell21_1731683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 3].length) (baseStart_1731683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731683 prefixEnd_1731683 := by exact prefixLift 1731683
  have htrace : WordTrace (prefixWord ++ tailWord_1731683) baseStart_1731683 baseEnd_1731683 := by
    simpa [prefixWord, tailWord_1731683, baseEnd_1731683] using wordTrace_append hprefix tailTrace_1731683
  have hstable : (prefixWord ++ tailWord_1731683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731683).length < 2 ^ (prefixWord ++ tailWord_1731683).sum := by decide
  have hdescent : baseEnd_1731683 < baseStart_1731683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731759 : List Nat := [1, 1, 2, 1, 2, 3, 4, 4, 3]
def baseStart_1731759 : Nat := 118140960795 + 1731759 * 2 ^ 59
def prefixEnd_1731759 : Nat := 4983230072969 + 3 ^ 40 * 1731759 * 2
def baseEnd_1731759 : Nat := 395210997666486763843685

theorem tailTrace_1731759 : CollatzResearch.WordTrace tailWord_1731759 prefixEnd_1731759 395210997666486763843685 := by
  unfold tailWord_1731759
  simp only [CollatzResearch.WordTrace]
  refine ⟨63162439733140378735582331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42108293155426919157054887 63162439733140378735582331)
  ·
    refine ⟨94743659599710568103373497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63162439733140378735582331 94743659599710568103373497)
    ·
      refine ⟨71057744699782926077530123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94743659599710568103373497 71057744699782926077530123)
      ·
        refine ⟨106586617049674389116295185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71057744699782926077530123 106586617049674389116295185)
        ·
          refine ⟨79939962787255791837221389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106586617049674389116295185 79939962787255791837221389)
          ·
            refine ⟨29977486045220921938958021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79939962787255791837221389 29977486045220921938958021)
            ·
              refine ⟨5620778633478922863554629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29977486045220921938958021 5620778633478922863554629)
              ·
                refine ⟨1053895993777298036916493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5620778633478922863554629 1053895993777298036916493)
                ·
                  refine ⟨395210997666486763843685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053895993777298036916493 395210997666486763843685)
                  ·
                    rfl

theorem cell21_1731759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 3].length) (baseStart_1731759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731759 prefixEnd_1731759 := by exact prefixLift 1731759
  have htrace : WordTrace (prefixWord ++ tailWord_1731759) baseStart_1731759 baseEnd_1731759 := by
    simpa [prefixWord, tailWord_1731759, baseEnd_1731759] using wordTrace_append hprefix tailTrace_1731759
  have hstable : (prefixWord ++ tailWord_1731759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731759).length < 2 ^ (prefixWord ++ tailWord_1731759).sum := by decide
  have hdescent : baseEnd_1731759 < baseStart_1731759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731773 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1731773 : Nat := 118140960795 + 1731773 * 2 ^ 59
def prefixEnd_1731773 : Nat := 4983230072969 + 3 ^ 40 * 1731773 * 2
def baseEnd_1731773 : Nat := 395214192657225850610323

theorem tailTrace_1731773 : CollatzResearch.WordTrace tailWord_1731773 prefixEnd_1731773 395214192657225850610323 := by
  unfold tailWord_1731773
  simp only [CollatzResearch.WordTrace]
  refine ⟨63162950355089659126591973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42108633570059772751061315 63162950355089659126591973)
  ·
    refine ⟨11843053191579311086235995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63162950355089659126591973 11843053191579311086235995)
    ·
      refine ⟨17764579787368966629353993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11843053191579311086235995 17764579787368966629353993)
      ·
        refine ⟨13323434840526724972015495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17764579787368966629353993 13323434840526724972015495)
        ·
          refine ⟨19985152260790087458023243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13323434840526724972015495 19985152260790087458023243)
          ·
            refine ⟨29977728391185131187034865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19985152260790087458023243 29977728391185131187034865)
            ·
              refine ⟨22483296293388848390276149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29977728391185131187034865 22483296293388848390276149)
              ·
                refine ⟨2107809027505204536588389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22483296293388848390276149 2107809027505204536588389)
                ·
                  refine ⟨395214192657225850610323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2107809027505204536588389 395214192657225850610323)
                  ·
                    rfl

theorem cell21_1731773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1731773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731773 prefixEnd_1731773 := by exact prefixLift 1731773
  have htrace : WordTrace (prefixWord ++ tailWord_1731773) baseStart_1731773 baseEnd_1731773 := by
    simpa [prefixWord, tailWord_1731773, baseEnd_1731773] using wordTrace_append hprefix tailTrace_1731773
  have hstable : (prefixWord ++ tailWord_1731773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731773).length < 2 ^ (prefixWord ++ tailWord_1731773).sum := by decide
  have hdescent : baseEnd_1731773 < baseStart_1731773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731866 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_1731866 : Nat := 118140960795 + 1731866 * 2 ^ 59
def prefixEnd_1731866 : Nat := 4983230072969 + 3 ^ 40 * 1731866 * 2
def baseEnd_1731866 : Nat := 395235416524278355560133

theorem tailTrace_1731866 : CollatzResearch.WordTrace tailWord_1731866 prefixEnd_1731866 395235416524278355560133 := by
  unfold tailWord_1731866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15791585585938184002431863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42110894895835157339818301 15791585585938184002431863)
  ·
    refine ⟨23687378378907276003647795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15791585585938184002431863 23687378378907276003647795)
    ·
      refine ⟨35531067568360914005471693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23687378378907276003647795 35531067568360914005471693)
      ·
        refine ⟨13324150338135342752051885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35531067568360914005471693 13324150338135342752051885)
        ·
          refine ⟨4996556376800753532019457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13324150338135342752051885 4996556376800753532019457)
          ·
            refine ⟨3747417282600565149014593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4996556376800753532019457 3747417282600565149014593)
            ·
              refine ⟨2810562961950423861760945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3747417282600565149014593 2810562961950423861760945)
              ·
                refine ⟨2107922221462817896320709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810562961950423861760945 2107922221462817896320709)
                ·
                  refine ⟨395235416524278355560133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2107922221462817896320709 395235416524278355560133)
                  ·
                    rfl

theorem cell21_1731866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_1731866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731866 prefixEnd_1731866 := by exact prefixLift 1731866
  have htrace : WordTrace (prefixWord ++ tailWord_1731866) baseStart_1731866 baseEnd_1731866 := by
    simpa [prefixWord, tailWord_1731866, baseEnd_1731866] using wordTrace_append hprefix tailTrace_1731866
  have hstable : (prefixWord ++ tailWord_1731866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731866).length < 2 ^ (prefixWord ++ tailWord_1731866).sum := by decide
  have hdescent : baseEnd_1731866 < baseStart_1731866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731869 : List Nat := [1, 4, 2, 3, 1, 1, 4, 2, 3]
def baseStart_1731869 : Nat := 118140960795 + 1731869 * 2 ^ 59
def prefixEnd_1731869 : Nat := 4983230072969 + 3 ^ 40 * 1731869 * 2
def baseEnd_1731869 : Nat := 395236101165151017010127

theorem tailTrace_1731869 : CollatzResearch.WordTrace tailWord_1731869 prefixEnd_1731869 395236101165151017010127 := by
  unfold tailWord_1731869
  simp only [CollatzResearch.WordTrace]
  refine ⟨63166451762741867522086661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42110967841827911681391107 63166451762741867522086661)
  ·
    refine ⟨11843709705514100160391249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63166451762741867522086661 11843709705514100160391249)
    ·
      refine ⟨8882782279135575120293437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11843709705514100160391249 8882782279135575120293437)
      ·
        refine ⟨3331043354675840670110039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8882782279135575120293437 3331043354675840670110039)
        ·
          refine ⟨4996565032013761005165059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331043354675840670110039 4996565032013761005165059)
          ·
            refine ⟨7494847548020641507747589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996565032013761005165059 7494847548020641507747589)
            ·
              refine ⟨1405283915253870282702673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7494847548020641507747589 1405283915253870282702673)
              ·
                refine ⟨1053962936440402712027005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405283915253870282702673 1053962936440402712027005)
                ·
                  refine ⟨395236101165151017010127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053962936440402712027005 395236101165151017010127)
                  ·
                    rfl

theorem cell21_1731869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_1731869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731869 prefixEnd_1731869 := by exact prefixLift 1731869
  have htrace : WordTrace (prefixWord ++ tailWord_1731869) baseStart_1731869 baseEnd_1731869 := by
    simpa [prefixWord, tailWord_1731869, baseEnd_1731869] using wordTrace_append hprefix tailTrace_1731869
  have hstable : (prefixWord ++ tailWord_1731869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731869).length < 2 ^ (prefixWord ++ tailWord_1731869).sum := by decide
  have hdescent : baseEnd_1731869 < baseStart_1731869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731880 : List Nat := [2, 1, 5, 1, 2, 1, 3, 6]
def baseStart_1731880 : Nat := 118140960795 + 1731880 * 2 ^ 59
def prefixEnd_1731880 : Nat := 4983230072969 + 3 ^ 40 * 1731880 * 2
def baseEnd_1731880 : Nat := 131746203838339147442257

theorem tailTrace_1731880 : CollatzResearch.WordTrace tailWord_1731880 prefixEnd_1731880 131746203838339147442257 := by
  unfold tailWord_1731880
  simp only [CollatzResearch.WordTrace]
  refine ⟨31583426482851008200368547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42111235310468010933824729 31583426482851008200368547)
  ·
    refine ⟨47375139724276512300552821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31583426482851008200368547 47375139724276512300552821)
    ·
      refine ⟨4441419349150923028176827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47375139724276512300552821 4441419349150923028176827)
      ·
        refine ⟨6662129023726384542265241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4441419349150923028176827 6662129023726384542265241)
        ·
          refine ⟨4996596767794788406698931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6662129023726384542265241 4996596767794788406698931)
          ·
            refine ⟨7494895151692182610048397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996596767794788406698931 7494895151692182610048397)
            ·
              refine ⟨2810585681884568478768149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7494895151692182610048397 2810585681884568478768149)
              ·
                refine ⟨131746203838339147442257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2810585681884568478768149 131746203838339147442257)
                ·
                  rfl

theorem cell21_1731880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_1731880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731880 prefixEnd_1731880 := by exact prefixLift 1731880
  have htrace : WordTrace (prefixWord ++ tailWord_1731880) baseStart_1731880 baseEnd_1731880 := by
    simpa [prefixWord, tailWord_1731880, baseEnd_1731880] using wordTrace_append hprefix tailTrace_1731880
  have hstable : (prefixWord ++ tailWord_1731880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731880).length < 2 ^ (prefixWord ++ tailWord_1731880).sum := by decide
  have hdescent : baseEnd_1731880 < baseStart_1731880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731897 : List Nat := [1, 2, 1, 6, 2, 1, 3, 5]
def baseStart_1731897 : Nat := 118140960795 + 1731897 * 2 ^ 59
def prefixEnd_1731897 : Nat := 4983230072969 + 3 ^ 40 * 1731897 * 2
def baseEnd_1731897 : Nat := 131747497048876396847801

theorem tailTrace_1731897 : CollatzResearch.WordTrace tailWord_1731897 prefixEnd_1731897 131747497048876396847801 := by
  unfold tailWord_1731897
  simp only [CollatzResearch.WordTrace]
  refine ⟨63167473006640428304105945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42111648671093618869403963 63167473006640428304105945)
  ·
    refine ⟨47375604754980321228079459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63167473006640428304105945 47375604754980321228079459)
    ·
      refine ⟨71063407132470481842119189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47375604754980321228079459 71063407132470481842119189)
      ·
        refine ⟨3331097209334553836349337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71063407132470481842119189 3331097209334553836349337)
        ·
          refine ⟨2498322907000915377262003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3331097209334553836349337 2498322907000915377262003)
          ·
            refine ⟨3747484360501373065893005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498322907000915377262003 3747484360501373065893005)
            ·
              refine ⟨1405306635188014899709877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3747484360501373065893005 1405306635188014899709877)
              ·
                refine ⟨131747497048876396847801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1405306635188014899709877 131747497048876396847801)
                ·
                  rfl

theorem cell21_1731897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 5].length) (baseStart_1731897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731897 prefixEnd_1731897 := by exact prefixLift 1731897
  have htrace : WordTrace (prefixWord ++ tailWord_1731897) baseStart_1731897 baseEnd_1731897 := by
    simpa [prefixWord, tailWord_1731897, baseEnd_1731897] using wordTrace_append hprefix tailTrace_1731897
  have hstable : (prefixWord ++ tailWord_1731897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731897).length < 2 ^ (prefixWord ++ tailWord_1731897).sum := by decide
  have hdescent : baseEnd_1731897 < baseStart_1731897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731911 : List Nat := [1, 1, 4, 1, 2, 3, 1, 5, 3]
def baseStart_1731911 : Nat := 118140960795 + 1731911 * 2 ^ 59
def prefixEnd_1731911 : Nat := 4983230072969 + 3 ^ 40 * 1731911 * 2
def baseEnd_1731911 : Nat := 395245686137368277310041

theorem tailTrace_1731911 : CollatzResearch.WordTrace tailWord_1731911 prefixEnd_1731911 395245686137368277310041 := by
  unfold tailWord_1731911
  simp only [CollatzResearch.WordTrace]
  refine ⟨63167983628589708695115587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42111989085726472463410391 63167983628589708695115587)
  ·
    refine ⟨94751975442884563042673381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63167983628589708695115587 94751975442884563042673381)
    ·
      refine ⟨17765995395540855570501259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94751975442884563042673381 17765995395540855570501259)
      ·
        refine ⟨26648993093311283355751889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17765995395540855570501259 26648993093311283355751889)
        ·
          refine ⟨19986744819983462516813917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26648993093311283355751889 19986744819983462516813917)
          ·
            refine ⟨7495029307493798443805219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19986744819983462516813917 7495029307493798443805219)
            ·
              refine ⟨11242543961240697665707829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495029307493798443805219 11242543961240697665707829)
              ·
                refine ⟨1053988496366315406160109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11242543961240697665707829 1053988496366315406160109)
                ·
                  refine ⟨395245686137368277310041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053988496366315406160109 395245686137368277310041)
                  ·
                    rfl

theorem cell21_1731911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 3].length) (baseStart_1731911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731911 prefixEnd_1731911 := by exact prefixLift 1731911
  have htrace : WordTrace (prefixWord ++ tailWord_1731911) baseStart_1731911 baseEnd_1731911 := by
    simpa [prefixWord, tailWord_1731911, baseEnd_1731911] using wordTrace_append hprefix tailTrace_1731911
  have hstable : (prefixWord ++ tailWord_1731911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731911).length < 2 ^ (prefixWord ++ tailWord_1731911).sum := by decide
  have hdescent : baseEnd_1731911 < baseStart_1731911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731917 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1731917 : Nat := 118140960795 + 1731917 * 2 ^ 59
def prefixEnd_1731917 : Nat := 4983230072969 + 3 ^ 40 * 1731917 * 2
def baseEnd_1731917 : Nat := 395247055419113600210029

theorem tailTrace_1731917 : CollatzResearch.WordTrace tailWord_1731917 prefixEnd_1731917 395247055419113600210029 := by
  unfold tailWord_1731917
  simp only [CollatzResearch.WordTrace]
  refine ⟨63168202466567971719834005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42112134977711981146556003 63168202466567971719834005)
  ·
    refine ⟨2961009490620373674367219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63168202466567971719834005 2961009490620373674367219)
    ·
      refine ⟨4441514235930560511550829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961009490620373674367219 4441514235930560511550829)
      ·
        refine ⟨1665567838473960191831561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4441514235930560511550829 1665567838473960191831561)
        ·
          refine ⟨1249175878855470143873671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1665567838473960191831561 1249175878855470143873671)
          ·
            refine ⟨1873763818283205215810507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249175878855470143873671 1873763818283205215810507)
            ·
              refine ⟨2810645727424807823715761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873763818283205215810507 2810645727424807823715761)
              ·
                refine ⟨2107984295568605867786821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810645727424807823715761 2107984295568605867786821)
                ·
                  refine ⟨395247055419113600210029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2107984295568605867786821 395247055419113600210029)
                  ·
                    rfl

theorem cell21_1731917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1731917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731917 prefixEnd_1731917 := by exact prefixLift 1731917
  have htrace : WordTrace (prefixWord ++ tailWord_1731917) baseStart_1731917 baseEnd_1731917 := by
    simpa [prefixWord, tailWord_1731917, baseEnd_1731917] using wordTrace_append hprefix tailTrace_1731917
  have hstable : (prefixWord ++ tailWord_1731917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731917).length < 2 ^ (prefixWord ++ tailWord_1731917).sum := by decide
  have hdescent : baseEnd_1731917 < baseStart_1731917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1731925 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 6]
def baseStart_1731925 : Nat := 118140960795 + 1731925 * 2 ^ 59
def prefixEnd_1731925 : Nat := 4983230072969 + 3 ^ 40 * 1731925 * 2
def baseEnd_1731925 : Nat := 395248881128107364076679

theorem tailTrace_1731925 : CollatzResearch.WordTrace tailWord_1731925 prefixEnd_1731925 395248881128107364076679 := by
  unfold tailWord_1731925
  simp only [CollatzResearch.WordTrace]
  refine ⟨63168494250538989086125229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42112329500359326057416819 63168494250538989086125229)
  ·
    refine ⟨23688185343952120907296961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63168494250538989086125229 23688185343952120907296961)
    ·
      refine ⟨17766139007964090680472721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23688185343952120907296961 17766139007964090680472721)
      ·
        refine ⟨13324604255973068010354541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17766139007964090680472721 13324604255973068010354541)
        ·
          refine ⟨4996726595989900503882953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13324604255973068010354541 4996726595989900503882953)
          ·
            refine ⟨3747544946992425377912215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4996726595989900503882953 3747544946992425377912215)
            ·
              refine ⟨5621317420488638066868323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747544946992425377912215 5621317420488638066868323)
              ·
                refine ⟨8431976130732957100302485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5621317420488638066868323 8431976130732957100302485)
                ·
                  refine ⟨395248881128107364076679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8431976130732957100302485 395248881128107364076679)
                  ·
                    rfl

theorem cell21_1731925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_1731925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1731925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1731925 prefixEnd_1731925 := by exact prefixLift 1731925
  have htrace : WordTrace (prefixWord ++ tailWord_1731925) baseStart_1731925 baseEnd_1731925 := by
    simpa [prefixWord, tailWord_1731925, baseEnd_1731925] using wordTrace_append hprefix tailTrace_1731925
  have hstable : (prefixWord ++ tailWord_1731925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1731925).length < 2 ^ (prefixWord ++ tailWord_1731925).sum := by decide
  have hdescent : baseEnd_1731925 < baseStart_1731925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1731925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732156 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 5]
def baseStart_1732156 : Nat := 118140960795 + 1732156 * 2 ^ 59
def prefixEnd_1732156 : Nat := 4983230072969 + 3 ^ 40 * 1732156 * 2
def baseEnd_1732156 : Nat := 395301598475302295726207

theorem tailTrace_1732156 : CollatzResearch.WordTrace tailWord_1732156 prefixEnd_1732156 395301598475302295726207 := by
  unfold tailWord_1732156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31588459756351057768892161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42117946341801410358522881 31588459756351057768892161)
  ·
    refine ⟨23691344817263293326669121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31588459756351057768892161 23691344817263293326669121)
    ·
      refine ⟨17768508612947469995001841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23691344817263293326669121 17768508612947469995001841)
      ·
        refine ⟨13326381459710602496251381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17768508612947469995001841 13326381459710602496251381)
        ·
          refine ⟨1249348261847868984023567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13326381459710602496251381 1249348261847868984023567)
          ·
            refine ⟨1874022392771803476035351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249348261847868984023567 1874022392771803476035351)
            ·
              refine ⟨2811033589157705214053027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874022392771803476035351 2811033589157705214053027)
              ·
                refine ⟨4216550383736557821079541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811033589157705214053027 4216550383736557821079541)
                ·
                  refine ⟨395301598475302295726207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4216550383736557821079541 395301598475302295726207)
                  ·
                    rfl

theorem cell21_1732156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_1732156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732156 prefixEnd_1732156 := by exact prefixLift 1732156
  have htrace : WordTrace (prefixWord ++ tailWord_1732156) baseStart_1732156 baseEnd_1732156 := by
    simpa [prefixWord, tailWord_1732156, baseEnd_1732156] using wordTrace_append hprefix tailTrace_1732156
  have hstable : (prefixWord ++ tailWord_1732156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732156).length < 2 ^ (prefixWord ++ tailWord_1732156).sum := by decide
  have hdescent : baseEnd_1732156 < baseStart_1732156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732181 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1732181 : Nat := 118140960795 + 1732181 * 2 ^ 59
def prefixEnd_1732181 : Nat := 4983230072969 + 3 ^ 40 * 1732181 * 2
def baseEnd_1732181 : Nat := 395307303815907807809489

theorem tailTrace_1732181 : CollatzResearch.WordTrace tailWord_1732181 prefixEnd_1732181 395307303815907807809489 := by
  unfold tailWord_1732181
  simp only [CollatzResearch.WordTrace]
  refine ⟨63177831337611544807444397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42118554225074363204962931 63177831337611544807444397)
  ·
    refine ⟨23691686751604329302791649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63177831337611544807444397 23691686751604329302791649)
    ·
      refine ⟨17768765063703246977093737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23691686751604329302791649 17768765063703246977093737)
      ·
        refine ⟨13326573797777435232820303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17768765063703246977093737 13326573797777435232820303)
        ·
          refine ⟨19989860696666152849230455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13326573797777435232820303 19989860696666152849230455)
          ·
            refine ⟨29984791044999229273845683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19989860696666152849230455 29984791044999229273845683)
            ·
              refine ⟨44977186567498843910768525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29984791044999229273845683 44977186567498843910768525)
              ·
                refine ⟨16866444962812066466538197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44977186567498843910768525 16866444962812066466538197)
                ·
                  refine ⟨395307303815907807809489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16866444962812066466538197 395307303815907807809489)
                  ·
                    rfl

theorem cell21_1732181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1732181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732181 prefixEnd_1732181 := by exact prefixLift 1732181
  have htrace : WordTrace (prefixWord ++ tailWord_1732181) baseStart_1732181 baseEnd_1732181 := by
    simpa [prefixWord, tailWord_1732181, baseEnd_1732181] using wordTrace_append hprefix tailTrace_1732181
  have hstable : (prefixWord ++ tailWord_1732181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732181).length < 2 ^ (prefixWord ++ tailWord_1732181).sum := by decide
  have hdescent : baseEnd_1732181 < baseStart_1732181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732294 : List Nat := [6, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1732294 : Nat := 118140960795 + 1732294 * 2 ^ 59
def prefixEnd_1732294 : Nat := 4983230072969 + 3 ^ 40 * 1732294 * 2
def baseEnd_1732294 : Nat := 131777697318481574141975

theorem tailTrace_1732294 : CollatzResearch.WordTrace tailWord_1732294 prefixEnd_1732294 131777697318481574141975 := by
  unfold tailWord_1732294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974436024568817659572123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42121301857468110070871957 1974436024568817659572123)
  ·
    refine ⟨2961654036853226489358185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974436024568817659572123 2961654036853226489358185)
    ·
      refine ⟨2221240527639919867018639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2961654036853226489358185 2221240527639919867018639)
      ·
        refine ⟨3331860791459879800527959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221240527639919867018639 3331860791459879800527959)
        ·
          refine ⟨4997791187189819700791939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331860791459879800527959 4997791187189819700791939)
          ·
            refine ⟨7496686780784729551187909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997791187189819700791939 7496686780784729551187909)
            ·
              refine ⟨1405628771397136790847733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7496686780784729551187909 1405628771397136790847733)
              ·
                refine ⟨131777697318481574141975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1405628771397136790847733 131777697318481574141975)
                ·
                  rfl

theorem cell21_1732294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1732294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732294 prefixEnd_1732294 := by exact prefixLift 1732294
  have htrace : WordTrace (prefixWord ++ tailWord_1732294) baseStart_1732294 baseEnd_1732294 := by
    simpa [prefixWord, tailWord_1732294, baseEnd_1732294] using wordTrace_append hprefix tailTrace_1732294
  have hstable : (prefixWord ++ tailWord_1732294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732294).length < 2 ^ (prefixWord ++ tailWord_1732294).sum := by decide
  have hdescent : baseEnd_1732294 < baseStart_1732294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732308 : List Nat := [2, 4, 1, 3, 1, 1, 3, 3, 3]
def baseStart_1732308 : Nat := 118140960795 + 1732308 * 2 ^ 59
def prefixEnd_1732308 : Nat := 4983230072969 + 3 ^ 40 * 1732308 * 2
def baseEnd_1732308 : Nat := 395336286946183809192563

theorem tailTrace_1732308 : CollatzResearch.WordTrace tailWord_1732308 prefixEnd_1732308 395336286946183809192563 := by
  unfold tailWord_1732308
  simp only [CollatzResearch.WordTrace]
  refine ⟨31591231704075722748658789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42121642272100963664878385 31591231704075722748658789)
  ·
    refine ⟨5923355944514198015373523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31591231704075722748658789 5923355944514198015373523)
    ·
      refine ⟨8885033916771297023060285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5923355944514198015373523 8885033916771297023060285)
      ·
        refine ⟨3331887718789236383647607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8885033916771297023060285 3331887718789236383647607)
        ·
          refine ⟨4997831578183854575471411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331887718789236383647607 4997831578183854575471411)
          ·
            refine ⟨7496747367275781863207117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997831578183854575471411 7496747367275781863207117)
            ·
              refine ⟨2811280262728418198702669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7496747367275781863207117 2811280262728418198702669)
              ·
                refine ⟨1054230098523156824513501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2811280262728418198702669 1054230098523156824513501)
                ·
                  refine ⟨395336286946183809192563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054230098523156824513501 395336286946183809192563)
                  ·
                    rfl

theorem cell21_1732308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_1732308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732308 prefixEnd_1732308 := by exact prefixLift 1732308
  have htrace : WordTrace (prefixWord ++ tailWord_1732308) baseStart_1732308 baseEnd_1732308 := by
    simpa [prefixWord, tailWord_1732308, baseEnd_1732308] using wordTrace_append hprefix tailTrace_1732308
  have hstable : (prefixWord ++ tailWord_1732308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732308).length < 2 ^ (prefixWord ++ tailWord_1732308).sum := by decide
  have hdescent : baseEnd_1732308 < baseStart_1732308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732347 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 8]
def baseStart_1732347 : Nat := 118140960795 + 1732347 * 2 ^ 59
def prefixEnd_1732347 : Nat := 4983230072969 + 3 ^ 40 * 1732347 * 2
def baseEnd_1732347 : Nat := 395345187277528408042483

theorem tailTrace_1732347 : CollatzResearch.WordTrace tailWord_1732347 prefixEnd_1732347 395345187277528408042483 := by
  unfold tailWord_1732347
  simp only [CollatzResearch.WordTrace]
  refine ⟨63183885855010155157987295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42122590570006770105324863 63183885855010155157987295)
  ·
    refine ⟨94775828782515232736980943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63183885855010155157987295 94775828782515232736980943)
    ·
      refine ⟨142163743173772849105471415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94775828782515232736980943 142163743173772849105471415)
      ·
        refine ⟨213245614760659273658207123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142163743173772849105471415 213245614760659273658207123)
        ·
          refine ⟨319868422140988910487310685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213245614760659273658207123 319868422140988910487310685)
          ·
            refine ⟨119950658302870841432741507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319868422140988910487310685 119950658302870841432741507)
            ·
              refine ⟨179925987454306262149112261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119950658302870841432741507 179925987454306262149112261)
              ·
                refine ⟨33736122647682424152958549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179925987454306262149112261 33736122647682424152958549)
                ·
                  refine ⟨395345187277528408042483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33736122647682424152958549 395345187277528408042483)
                  ·
                    rfl

theorem cell21_1732347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_1732347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732347 prefixEnd_1732347 := by exact prefixLift 1732347
  have htrace : WordTrace (prefixWord ++ tailWord_1732347) baseStart_1732347 baseEnd_1732347 := by
    simpa [prefixWord, tailWord_1732347, baseEnd_1732347] using wordTrace_append hprefix tailTrace_1732347
  have hstable : (prefixWord ++ tailWord_1732347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732347).length < 2 ^ (prefixWord ++ tailWord_1732347).sum := by decide
  have hdescent : baseEnd_1732347 < baseStart_1732347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732378 : List Nat := [3, 1, 1, 3, 2, 11]
def baseStart_1732378 : Nat := 118140960795 + 1732378 * 2 ^ 59
def prefixEnd_1732378 : Nat := 4983230072969 + 3 ^ 40 * 1732378 * 2
def baseEnd_1732378 : Nat := 14642676366662194186139

theorem tailTrace_1732378 : CollatzResearch.WordTrace tailWord_1732378 prefixEnd_1732378 14642676366662194186139 := by
  unfold tailWord_1732378
  simp only [CollatzResearch.WordTrace]
  refine ⟨15796254129474461863091447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42123344345265231634910525 15796254129474461863091447)
  ·
    refine ⟨23694381194211692794637171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15796254129474461863091447 23694381194211692794637171)
    ·
      refine ⟨35541571791317539191955757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23694381194211692794637171 35541571791317539191955757)
      ·
        refine ⟨13328089421744077196983409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35541571791317539191955757 13328089421744077196983409)
        ·
          refine ⟨9996067066308057897737557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13328089421744077196983409 9996067066308057897737557)
          ·
            refine ⟨14642676366662194186139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9996067066308057897737557 14642676366662194186139)
            ·
              rfl

theorem cell21_1732378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 11].length) (baseStart_1732378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732378 prefixEnd_1732378 := by exact prefixLift 1732378
  have htrace : WordTrace (prefixWord ++ tailWord_1732378) baseStart_1732378 baseEnd_1732378 := by
    simpa [prefixWord, tailWord_1732378, baseEnd_1732378] using wordTrace_append hprefix tailTrace_1732378
  have hstable : (prefixWord ++ tailWord_1732378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732378).length < 2 ^ (prefixWord ++ tailWord_1732378).sum := by decide
  have hdescent : baseEnd_1732378 < baseStart_1732378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732488 : List Nat := [2, 1, 3, 3, 4, 1, 7]
def baseStart_1732488 : Nat := 118140960795 + 1732488 * 2 ^ 59
def prefixEnd_1732488 : Nat := 4983230072969 + 3 ^ 40 * 1732488 * 2
def baseEnd_1732488 : Nat := 43930818377615944021355

theorem tailTrace_1732488 : CollatzResearch.WordTrace tailWord_1732488 prefixEnd_1732488 43930818377615944021355 := by
  unfold tailWord_1732488
  simp only [CollatzResearch.WordTrace]
  refine ⟨31594514273749668119435059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42126019031666224159246745 31594514273749668119435059)
  ·
    refine ⟨47391771410624502179152589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31594514273749668119435059 47391771410624502179152589)
    ·
      refine ⟨17771914278984188317182221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47391771410624502179152589 17771914278984188317182221)
      ·
        refine ⟨6664467854619070618943333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17771914278984188317182221 6664467854619070618943333)
        ·
          refine ⟨1249587722741075741051875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6664467854619070618943333 1249587722741075741051875)
          ·
            refine ⟨1874381584111613611577813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249587722741075741051875 1874381584111613611577813)
            ·
              refine ⟨43930818377615944021355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1874381584111613611577813 43930818377615944021355)
              ·
                rfl

theorem cell21_1732488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 7].length) (baseStart_1732488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732488 prefixEnd_1732488 := by exact prefixLift 1732488
  have htrace : WordTrace (prefixWord ++ tailWord_1732488) baseStart_1732488 baseEnd_1732488 := by
    simpa [prefixWord, tailWord_1732488, baseEnd_1732488] using wordTrace_append hprefix tailTrace_1732488
  have hstable : (prefixWord ++ tailWord_1732488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732488).length < 2 ^ (prefixWord ++ tailWord_1732488).sum := by decide
  have hdescent : baseEnd_1732488 < baseStart_1732488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732668 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_1732668 : Nat := 118140960795 + 1732668 * 2 ^ 59
def prefixEnd_1732668 : Nat := 4983230072969 + 3 ^ 40 * 1732668 * 2
def baseEnd_1732668 : Nat := 395418443850903183191827

theorem tailTrace_1732668 : CollatzResearch.WordTrace tailWord_1732668 prefixEnd_1732668 395418443850903183191827 := by
  unfold tailWord_1732668
  simp only [CollatzResearch.WordTrace]
  refine ⟨31597796843423613490211329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42130395791231484653615105 31597796843423613490211329)
  ·
    refine ⟨23698347632567710117658497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31597796843423613490211329 23698347632567710117658497)
    ·
      refine ⟨17773760724425782588243873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23698347632567710117658497 17773760724425782588243873)
      ·
        refine ⟨13330320543319336941182905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17773760724425782588243873 13330320543319336941182905)
        ·
          refine ⟨9997740407489502705887179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13330320543319336941182905 9997740407489502705887179)
          ·
            refine ⟨14996610611234254058830769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9997740407489502705887179 14996610611234254058830769)
            ·
              refine ⟨11247457958425690544123077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14996610611234254058830769 11247457958425690544123077)
              ·
                refine ⟨2108898367204816977023077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11247457958425690544123077 2108898367204816977023077)
                ·
                  refine ⟨395418443850903183191827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2108898367204816977023077 395418443850903183191827)
                  ·
                    rfl

theorem cell21_1732668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_1732668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732668 prefixEnd_1732668 := by exact prefixLift 1732668
  have htrace : WordTrace (prefixWord ++ tailWord_1732668) baseStart_1732668 baseEnd_1732668 := by
    simpa [prefixWord, tailWord_1732668, baseEnd_1732668] using wordTrace_append hprefix tailTrace_1732668
  have hstable : (prefixWord ++ tailWord_1732668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732668).length < 2 ^ (prefixWord ++ tailWord_1732668).sum := by decide
  have hdescent : baseEnd_1732668 < baseStart_1732668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732685 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1732685 : Nat := 118140960795 + 1732685 * 2 ^ 59
def prefixEnd_1732685 : Nat := 4983230072969 + 3 ^ 40 * 1732685 * 2
def baseEnd_1732685 : Nat := 395422323482514931408459

theorem tailTrace_1732685 : CollatzResearch.WordTrace tailWord_1732685 prefixEnd_1732685 395422323482514931408459 := by
  unfold tailWord_1732685
  simp only [CollatzResearch.WordTrace]
  refine ⟨63196213727785638883791509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42130809151857092589194339 63196213727785638883791509)
  ·
    refine ⟨2962322518489951822677727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63196213727785638883791509 2962322518489951822677727)
    ·
      refine ⟨4443483777734927734016591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962322518489951822677727 4443483777734927734016591)
      ·
        refine ⟨6665225666602391601024887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4443483777734927734016591 6665225666602391601024887)
        ·
          refine ⟨9997838499903587401537331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6665225666602391601024887 9997838499903587401537331)
          ·
            refine ⟨14996757749855381102305997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9997838499903587401537331 14996757749855381102305997)
            ·
              refine ⟨5623784156195767913364749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14996757749855381102305997 5623784156195767913364749)
              ·
                refine ⟨2108919058573412967511781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5623784156195767913364749 2108919058573412967511781)
                ·
                  refine ⟨395422323482514931408459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2108919058573412967511781 395422323482514931408459)
                  ·
                    rfl

theorem cell21_1732685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1732685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732685 prefixEnd_1732685 := by exact prefixLift 1732685
  have htrace : WordTrace (prefixWord ++ tailWord_1732685) baseStart_1732685 baseEnd_1732685 := by
    simpa [prefixWord, tailWord_1732685, baseEnd_1732685] using wordTrace_append hprefix tailTrace_1732685
  have hstable : (prefixWord ++ tailWord_1732685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732685).length < 2 ^ (prefixWord ++ tailWord_1732685).sum := by decide
  have hdescent : baseEnd_1732685 < baseStart_1732685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732775 : List Nat := [1, 1, 6, 2, 2, 1, 8]
def baseStart_1732775 : Nat := 118140960795 + 1732775 * 2 ^ 59
def prefixEnd_1732775 : Nat := 4983230072969 + 3 ^ 40 * 1732775 * 2
def baseEnd_1732775 : Nat := 43938095856521641656475

theorem tailTrace_1732775 : CollatzResearch.WordTrace tailWord_1732775 prefixEnd_1732775 43938095856521641656475 := by
  unfold tailWord_1732775
  simp only [CollatzResearch.WordTrace]
  refine ⟨63199496297459584254567779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42132997531639722836378519 63199496297459584254567779)
  ·
    refine ⟨94799244446189376381851669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63199496297459584254567779 94799244446189376381851669)
    ·
      refine ⟨4443714583415127017899297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94799244446189376381851669 4443714583415127017899297)
      ·
        refine ⟨3332785937561345263424473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4443714583415127017899297 3332785937561345263424473)
        ·
          refine ⟨2499589453171008947568355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3332785937561345263424473 2499589453171008947568355)
          ·
            refine ⟨3749384179756513421352533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499589453171008947568355 3749384179756513421352533)
            ·
              refine ⟨43938095856521641656475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3749384179756513421352533 43938095856521641656475)
              ·
                rfl

theorem cell21_1732775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 8].length) (baseStart_1732775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732775 prefixEnd_1732775 := by exact prefixLift 1732775
  have htrace : WordTrace (prefixWord ++ tailWord_1732775) baseStart_1732775 baseEnd_1732775 := by
    simpa [prefixWord, tailWord_1732775, baseEnd_1732775] using wordTrace_append hprefix tailTrace_1732775
  have hstable : (prefixWord ++ tailWord_1732775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732775).length < 2 ^ (prefixWord ++ tailWord_1732775).sum := by decide
  have hdescent : baseEnd_1732775 < baseStart_1732775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732896 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_1732896 : Nat := 118140960795 + 1732896 * 2 ^ 59
def prefixEnd_1732896 : Nat := 4983230072969 + 3 ^ 40 * 1732896 * 2
def baseEnd_1732896 : Nat := 395470476557225453391361

theorem tailTrace_1732896 : CollatzResearch.WordTrace tailWord_1732896 prefixEnd_1732896 395470476557225453391361 := by
  unfold tailWord_1732896
  simp only [CollatzResearch.WordTrace]
  refine ⟨31601954765010610959861271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42135939686680814613148361 31601954765010610959861271)
  ·
    refine ⟨47402932147515916439791907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31601954765010610959861271 47402932147515916439791907)
    ·
      refine ⟨71104398221273874659687861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47402932147515916439791907 71104398221273874659687861)
      ·
        refine ⟨6666037333244425749345737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71104398221273874659687861 6666037333244425749345737)
        ·
          refine ⟨4999527999933319312009303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6666037333244425749345737 4999527999933319312009303)
          ·
            refine ⟨7499291999899978968013955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4999527999933319312009303 7499291999899978968013955)
            ·
              refine ⟨11248937999849968452020933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7499291999899978968013955 11248937999849968452020933)
              ·
                refine ⟨2109175874971869084753925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11248937999849968452020933 2109175874971869084753925)
                ·
                  refine ⟨395470476557225453391361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2109175874971869084753925 395470476557225453391361)
                  ·
                    rfl

theorem cell21_1732896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_1732896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732896 prefixEnd_1732896 := by exact prefixLift 1732896
  have htrace : WordTrace (prefixWord ++ tailWord_1732896) baseStart_1732896 baseEnd_1732896 := by
    simpa [prefixWord, tailWord_1732896, baseEnd_1732896] using wordTrace_append hprefix tailTrace_1732896
  have hstable : (prefixWord ++ tailWord_1732896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732896).length < 2 ^ (prefixWord ++ tailWord_1732896).sum := by decide
  have hdescent : baseEnd_1732896 < baseStart_1732896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1732969 : List Nat := [1, 2, 1, 1, 1, 3, 4, 8]
def baseStart_1732969 : Nat := 118140960795 + 1732969 * 2 ^ 59
def prefixEnd_1732969 : Nat := 4983230072969 + 3 ^ 40 * 1732969 * 2
def baseEnd_1732969 : Nat := 131829045383931182891515

theorem tailTrace_1732969 : CollatzResearch.WordTrace tailWord_1732969 prefixEnd_1732969 131829045383931182891515 := by
  unfold tailWord_1732969
  simp only [CollatzResearch.WordTrace]
  refine ⟨63206572058756755387129961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42137714705837836924753307 63206572058756755387129961)
  ·
    refine ⟨47404929044067566540347471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63206572058756755387129961 47404929044067566540347471)
    ·
      refine ⟨71107393566101349810521207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47404929044067566540347471 71107393566101349810521207)
      ·
        refine ⟨106661090349152024715781811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71107393566101349810521207 106661090349152024715781811)
        ·
          refine ⟨159991635523728037073672717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106661090349152024715781811 159991635523728037073672717)
          ·
            refine ⟨59996863321398013902627269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159991635523728037073672717 59996863321398013902627269)
            ·
              refine ⟨11249411872762127606742613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59996863321398013902627269 11249411872762127606742613)
              ·
                refine ⟨131829045383931182891515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11249411872762127606742613 131829045383931182891515)
                ·
                  rfl

theorem cell21_1732969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 8].length) (baseStart_1732969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1732969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1732969 prefixEnd_1732969 := by exact prefixLift 1732969
  have htrace : WordTrace (prefixWord ++ tailWord_1732969) baseStart_1732969 baseEnd_1732969 := by
    simpa [prefixWord, tailWord_1732969, baseEnd_1732969] using wordTrace_append hprefix tailTrace_1732969
  have hstable : (prefixWord ++ tailWord_1732969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1732969).length < 2 ^ (prefixWord ++ tailWord_1732969).sum := by decide
  have hdescent : baseEnd_1732969 < baseStart_1732969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1732969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733062 : List Nat := [6, 1, 14]
def baseStart_1733062 : Nat := 118140960795 + 1733062 * 2 ^ 59
def prefixEnd_1733062 : Nat := 4983230072969 + 3 ^ 40 * 1733062 * 2
def baseEnd_1733062 : Nat := 542535473276880731995

theorem tailTrace_1733062 : CollatzResearch.WordTrace tailWord_1733062 prefixEnd_1733062 542535473276880731995 := by
  unfold tailWord_1733062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975311376481869758445795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42139976031613221513510293 1975311376481869758445795)
  ·
    refine ⟨2962967064722804637668693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1975311376481869758445795 2962967064722804637668693)
    ·
      refine ⟨542535473276880731995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 2962967064722804637668693 542535473276880731995)
      ·
        rfl

theorem cell21_1733062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 14].length) (baseStart_1733062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733062 prefixEnd_1733062 := by exact prefixLift 1733062
  have htrace : WordTrace (prefixWord ++ tailWord_1733062) baseStart_1733062 baseEnd_1733062 := by
    simpa [prefixWord, tailWord_1733062, baseEnd_1733062] using wordTrace_append hprefix tailTrace_1733062
  have hstable : (prefixWord ++ tailWord_1733062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733062).length < 2 ^ (prefixWord ++ tailWord_1733062).sum := by decide
  have hdescent : baseEnd_1733062 < baseStart_1733062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733068 : List Nat := [2, 2, 1, 4, 3, 2, 2, 2, 3]
def baseStart_1733068 : Nat := 118140960795 + 1733068 * 2 ^ 59
def prefixEnd_1733068 : Nat := 4983230072969 + 3 ^ 40 * 1733068 * 2
def baseEnd_1733068 : Nat := 395509729300591376524343

theorem tailTrace_1733068 : CollatzResearch.WordTrace tailWord_1733068 prefixEnd_1733068 395509729300591376524343 := by
  unfold tailWord_1733068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31605091442699047647491929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42140121923598730196655905 31605091442699047647491929)
  ·
    refine ⟨23703818582024285735618947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31605091442699047647491929 23703818582024285735618947)
    ·
      refine ⟨35555727873036428603428421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23703818582024285735618947 35555727873036428603428421)
      ·
        refine ⟨6666698976194330363142829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35555727873036428603428421 6666698976194330363142829)
        ·
          refine ⟨2500012116072873886178561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6666698976194330363142829 2500012116072873886178561)
          ·
            refine ⟨1875009087054655414633921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500012116072873886178561 1875009087054655414633921)
            ·
              refine ⟨1406256815290991560975441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875009087054655414633921 1406256815290991560975441)
              ·
                refine ⟨1054692611468243670731581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1406256815290991560975441 1054692611468243670731581)
                ·
                  refine ⟨395509729300591376524343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054692611468243670731581 395509729300591376524343)
                  ·
                    rfl

theorem cell21_1733068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_1733068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733068 prefixEnd_1733068 := by exact prefixLift 1733068
  have htrace : WordTrace (prefixWord ++ tailWord_1733068) baseStart_1733068 baseEnd_1733068 := by
    simpa [prefixWord, tailWord_1733068, baseEnd_1733068] using wordTrace_append hprefix tailTrace_1733068
  have hstable : (prefixWord ++ tailWord_1733068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733068).length < 2 ^ (prefixWord ++ tailWord_1733068).sum := by decide
  have hdescent : baseEnd_1733068 < baseStart_1733068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733124 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_1733124 : Nat := 118140960795 + 1733124 * 2 ^ 59
def prefixEnd_1733124 : Nat := 4983230072969 + 3 ^ 40 * 1733124 * 2
def baseEnd_1733124 : Nat := 395522509263547723590895

theorem tailTrace_1733124 : CollatzResearch.WordTrace tailWord_1733124 prefixEnd_1733124 395522509263547723590895 := by
  unfold tailWord_1733124
  simp only [CollatzResearch.WordTrace]
  refine ⟨31606112686597608429511213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42141483582130144572681617 31606112686597608429511213)
  ·
    refine ⟨11852292257474103161066705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31606112686597608429511213 11852292257474103161066705)
    ·
      refine ⟨8889219193105577370800029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11852292257474103161066705 8889219193105577370800029)
      ·
        refine ⟨3333457197414591514050011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8889219193105577370800029 3333457197414591514050011)
        ·
          refine ⟨5000185796121887271075017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333457197414591514050011 5000185796121887271075017)
          ·
            refine ⟨3750139347091415453306263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5000185796121887271075017 3750139347091415453306263)
            ·
              refine ⟨5625209020637123179959395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3750139347091415453306263 5625209020637123179959395)
              ·
                refine ⟨8437813530955684769939093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5625209020637123179959395 8437813530955684769939093)
                ·
                  refine ⟨395522509263547723590895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8437813530955684769939093 395522509263547723590895)
                  ·
                    rfl

theorem cell21_1733124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_1733124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733124 prefixEnd_1733124 := by exact prefixLift 1733124
  have htrace : WordTrace (prefixWord ++ tailWord_1733124) baseStart_1733124 baseEnd_1733124 := by
    simpa [prefixWord, tailWord_1733124, baseEnd_1733124] using wordTrace_append hprefix tailTrace_1733124
  have hstable : (prefixWord ++ tailWord_1733124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733124).length < 2 ^ (prefixWord ++ tailWord_1733124).sum := by decide
  have hdescent : baseEnd_1733124 < baseStart_1733124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733155 : List Nat := [1, 1, 1, 4, 4, 3, 2, 5]
def baseStart_1733155 : Nat := 118140960795 + 1733155 * 2 ^ 59
def prefixEnd_1733155 : Nat := 4983230072969 + 3 ^ 40 * 1733155 * 2
def baseEnd_1733155 : Nat := 131843194628632852858055

theorem tailTrace_1733155 : CollatzResearch.WordTrace tailWord_1733155 prefixEnd_1733155 131843194628632852858055 := by
  unfold tailWord_1733155
  simp only [CollatzResearch.WordTrace]
  refine ⟨63213356036082909153400919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42142237357388606102267279 63213356036082909153400919)
  ·
    refine ⟨94820034054124363730101379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63213356036082909153400919 94820034054124363730101379)
    ·
      refine ⟨142230051081186545595152069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94820034054124363730101379 142230051081186545595152069)
      ·
        refine ⟨26668134577722477299091013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142230051081186545595152069 26668134577722477299091013)
        ·
          refine ⟨5000275233322964493579565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26668134577722477299091013 5000275233322964493579565)
          ·
            refine ⟨1875103212496111685092337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5000275233322964493579565 1875103212496111685092337)
            ·
              refine ⟨1406327409372083763819253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875103212496111685092337 1406327409372083763819253)
              ·
                refine ⟨131843194628632852858055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1406327409372083763819253 131843194628632852858055)
                ·
                  rfl

theorem cell21_1733155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 5].length) (baseStart_1733155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733155 prefixEnd_1733155 := by exact prefixLift 1733155
  have htrace : WordTrace (prefixWord ++ tailWord_1733155) baseStart_1733155 baseEnd_1733155 := by
    simpa [prefixWord, tailWord_1733155, baseEnd_1733155] using wordTrace_append hprefix tailTrace_1733155
  have hstable : (prefixWord ++ tailWord_1733155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733155).length < 2 ^ (prefixWord ++ tailWord_1733155).sum := by decide
  have hdescent : baseEnd_1733155 < baseStart_1733155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733172 : List Nat := [2, 5, 1, 3, 1, 2, 7]
def baseStart_1733172 : Nat := 118140960795 + 1733172 * 2 ^ 59
def prefixEnd_1733172 : Nat := 4983230072969 + 3 ^ 40 * 1733172 * 2
def baseEnd_1733172 : Nat := 43948162613056700754533

theorem tailTrace_1733172 : CollatzResearch.WordTrace tailWord_1733172 prefixEnd_1733172 43948162613056700754533 := by
  unfold tailWord_1733172
  simp only [CollatzResearch.WordTrace]
  refine ⟨31606988038510660528384885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42142650718014214037846513 31606988038510660528384885)
  ·
    refine ⟨2963155128610374424536083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31606988038510660528384885 2963155128610374424536083)
    ·
      refine ⟨4444732692915561636804125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2963155128610374424536083 4444732692915561636804125)
      ·
        refine ⟨1666774759843335613801547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4444732692915561636804125 1666774759843335613801547)
        ·
          refine ⟨2500162139765003420702321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666774759843335613801547 2500162139765003420702321)
          ·
            refine ⟨1875121604823752565526741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500162139765003420702321 1875121604823752565526741)
            ·
              refine ⟨43948162613056700754533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1875121604823752565526741 43948162613056700754533)
              ·
                rfl

theorem cell21_1733172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 7].length) (baseStart_1733172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733172 prefixEnd_1733172 := by exact prefixLift 1733172
  have htrace : WordTrace (prefixWord ++ tailWord_1733172) baseStart_1733172 baseEnd_1733172 := by
    simpa [prefixWord, tailWord_1733172, baseEnd_1733172] using wordTrace_append hprefix tailTrace_1733172
  have hstable : (prefixWord ++ tailWord_1733172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733172).length < 2 ^ (prefixWord ++ tailWord_1733172).sum := by decide
  have hdescent : baseEnd_1733172 < baseStart_1733172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733183 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 4]
def baseStart_1733183 : Nat := 118140960795 + 1733183 * 2 ^ 59
def prefixEnd_1733183 : Nat := 4983230072969 + 3 ^ 40 * 1733183 * 2
def baseEnd_1733183 : Nat := 395535973867376732107441

theorem tailTrace_1733183 : CollatzResearch.WordTrace tailWord_1733183 prefixEnd_1733183 395535973867376732107441 := by
  unfold tailWord_1733183
  simp only [CollatzResearch.WordTrace]
  refine ⟨63214377279981469935420203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42142918186654313290280135 63214377279981469935420203)
  ·
    refine ⟨94821565919972204903130305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63214377279981469935420203 94821565919972204903130305)
    ·
      refine ⟨71116174439979153677347729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94821565919972204903130305 71116174439979153677347729)
      ·
        refine ⟨53337130829984365258010797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71116174439979153677347729 53337130829984365258010797)
        ·
          refine ⟨20001424061244136971754049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53337130829984365258010797 20001424061244136971754049)
          ·
            refine ⟨15001068045933102728815537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20001424061244136971754049 15001068045933102728815537)
            ·
              refine ⟨11250801034449827046611653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15001068045933102728815537 11250801034449827046611653)
              ·
                refine ⟨2109525193959342571239685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11250801034449827046611653 2109525193959342571239685)
                ·
                  refine ⟨395535973867376732107441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2109525193959342571239685 395535973867376732107441)
                  ·
                    rfl

theorem cell21_1733183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 4].length) (baseStart_1733183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733183 prefixEnd_1733183 := by exact prefixLift 1733183
  have htrace : WordTrace (prefixWord ++ tailWord_1733183) baseStart_1733183 baseEnd_1733183 := by
    simpa [prefixWord, tailWord_1733183, baseEnd_1733183] using wordTrace_append hprefix tailTrace_1733183
  have hstable : (prefixWord ++ tailWord_1733183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733183).length < 2 ^ (prefixWord ++ tailWord_1733183).sum := by decide
  have hdescent : baseEnd_1733183 < baseStart_1733183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733237 : List Nat := [1, 3, 4, 2, 3, 1, 2, 2, 3]
def baseStart_1733237 : Nat := 118140960795 + 1733237 * 2 ^ 59
def prefixEnd_1733237 : Nat := 4983230072969 + 3 ^ 40 * 1733237 * 2
def baseEnd_1733237 : Nat := 395548297403084638207331

theorem tailTrace_1733237 : CollatzResearch.WordTrace tailWord_1733237 prefixEnd_1733237 395548297403084638207331 := by
  unfold tailWord_1733237
  simp only [CollatzResearch.WordTrace]
  refine ⟨63216346821785837157885965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42144231214523891438590643 63216346821785837157885965)
  ·
    refine ⟨23706130058169688934207237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63216346821785837157885965 23706130058169688934207237)
    ·
      refine ⟨4444899385906816675163857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23706130058169688934207237 4444899385906816675163857)
      ·
        refine ⟨3333674539430112506372893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4444899385906816675163857 3333674539430112506372893)
        ·
          refine ⟨1250127952286292189889835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3333674539430112506372893 1250127952286292189889835)
          ·
            refine ⟨1875191928429438284834753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250127952286292189889835 1875191928429438284834753)
            ·
              refine ⟨1406393946322078713626065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875191928429438284834753 1406393946322078713626065)
              ·
                refine ⟨1054795459741559035219549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1406393946322078713626065 1054795459741559035219549)
                ·
                  refine ⟨395548297403084638207331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054795459741559035219549 395548297403084638207331)
                  ·
                    rfl

theorem cell21_1733237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_1733237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733237 prefixEnd_1733237 := by exact prefixLift 1733237
  have htrace : WordTrace (prefixWord ++ tailWord_1733237) baseStart_1733237 baseEnd_1733237 := by
    simpa [prefixWord, tailWord_1733237, baseEnd_1733237] using wordTrace_append hprefix tailTrace_1733237
  have hstable : (prefixWord ++ tailWord_1733237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733237).length < 2 ^ (prefixWord ++ tailWord_1733237).sum := by decide
  have hdescent : baseEnd_1733237 < baseStart_1733237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733242 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_1733242 : Nat := 118140960795 + 1733242 * 2 ^ 59
def prefixEnd_1733242 : Nat := 4983230072969 + 3 ^ 40 * 1733242 * 2
def baseEnd_1733242 : Nat := 395549438471205740623987

theorem tailTrace_1733242 : CollatzResearch.WordTrace tailWord_1733242 prefixEnd_1733242 395549438471205740623987 := by
  unfold tailWord_1733242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15804132296691930752954495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42144352791178482007878653 15804132296691930752954495)
  ·
    refine ⟨23706198445037896129431743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15804132296691930752954495 23706198445037896129431743)
    ·
      refine ⟨35559297667556844194147615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23706198445037896129431743 35559297667556844194147615)
      ·
        refine ⟨53338946501335266291221423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35559297667556844194147615 53338946501335266291221423)
        ·
          refine ⟨80008419752002899436832135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53338946501335266291221423 80008419752002899436832135)
          ·
            refine ⟨120012629628004349155248203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80008419752002899436832135 120012629628004349155248203)
            ·
              refine ⟨180018944442006523732872305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120012629628004349155248203 180018944442006523732872305)
              ·
                refine ⟨135014208331504892799654229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180018944442006523732872305 135014208331504892799654229)
                ·
                  refine ⟨395549438471205740623987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 135014208331504892799654229 395549438471205740623987)
                  ·
                    rfl

theorem cell21_1733242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_1733242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733242 prefixEnd_1733242 := by exact prefixLift 1733242
  have htrace : WordTrace (prefixWord ++ tailWord_1733242) baseStart_1733242 baseEnd_1733242 := by
    simpa [prefixWord, tailWord_1733242, baseEnd_1733242] using wordTrace_append hprefix tailTrace_1733242
  have hstable : (prefixWord ++ tailWord_1733242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733242).length < 2 ^ (prefixWord ++ tailWord_1733242).sum := by decide
  have hdescent : baseEnd_1733242 < baseStart_1733242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733293 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 4]
def baseStart_1733293 : Nat := 118140960795 + 1733293 * 2 ^ 59
def prefixEnd_1733293 : Nat := 4983230072969 + 3 ^ 40 * 1733293 * 2
def baseEnd_1733293 : Nat := 395561077366040985273883

theorem tailTrace_1733293 : CollatzResearch.WordTrace tailWord_1733293 prefixEnd_1733293 395561077366040985273883 := by
  unfold tailWord_1733293
  simp only [CollatzResearch.WordTrace]
  refine ⟨63218389309582958721924533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42145592873055305814616355 63218389309582958721924533)
  ·
    refine ⟨5926723997773402380180425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63218389309582958721924533 5926723997773402380180425)
    ·
      refine ⟨4445042998330051785135319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5926723997773402380180425 4445042998330051785135319)
      ·
        refine ⟨6667564497495077677702979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4445042998330051785135319 6667564497495077677702979)
        ·
          refine ⟨10001346746242616516554469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667564497495077677702979 10001346746242616516554469)
          ·
            refine ⟨1875252514920490596853963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10001346746242616516554469 1875252514920490596853963)
            ·
              refine ⟨2812878772380735895280945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875252514920490596853963 2812878772380735895280945)
              ·
                refine ⟨2109659079285551921460709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812878772380735895280945 2109659079285551921460709)
                ·
                  refine ⟨395561077366040985273883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2109659079285551921460709 395561077366040985273883)
                  ·
                    rfl

theorem cell21_1733293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_1733293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733293 prefixEnd_1733293 := by exact prefixLift 1733293
  have htrace : WordTrace (prefixWord ++ tailWord_1733293) baseStart_1733293 baseEnd_1733293 := by
    simpa [prefixWord, tailWord_1733293, baseEnd_1733293] using wordTrace_append hprefix tailTrace_1733293
  have hstable : (prefixWord ++ tailWord_1733293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733293).length < 2 ^ (prefixWord ++ tailWord_1733293).sum := by decide
  have hdescent : baseEnd_1733293 < baseStart_1733293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733349 : List Nat := [1, 3, 1, 4, 1, 2, 9]
def baseStart_1733349 : Nat := 118140960795 + 1733349 * 2 ^ 59
def prefixEnd_1733349 : Nat := 4983230072969 + 3 ^ 40 * 1733349 * 2
def baseEnd_1733349 : Nat := 43952650814333036926715

theorem tailTrace_1733349 : CollatzResearch.WordTrace tailWord_1733349 prefixEnd_1733349 43952650814333036926715 := by
  unfold tailWord_1733349
  simp only [CollatzResearch.WordTrace]
  refine ⟨63220431797380080285963101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42146954531586720190642067 63220431797380080285963101)
  ·
    refine ⟨23707661924017530107236163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63220431797380080285963101 23707661924017530107236163)
    ·
      refine ⟨35561492886026295160854245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23707661924017530107236163 35561492886026295160854245)
      ·
        refine ⟨6667779916129930342660171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35561492886026295160854245 6667779916129930342660171)
        ·
          refine ⟨10001669874194895513990257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667779916129930342660171 10001669874194895513990257)
          ·
            refine ⟨7501252405646171635492693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10001669874194895513990257 7501252405646171635492693)
            ·
              refine ⟨43952650814333036926715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7501252405646171635492693 43952650814333036926715)
              ·
                rfl

theorem cell21_1733349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 9].length) (baseStart_1733349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733349 prefixEnd_1733349 := by exact prefixLift 1733349
  have htrace : WordTrace (prefixWord ++ tailWord_1733349) baseStart_1733349 baseEnd_1733349 := by
    simpa [prefixWord, tailWord_1733349, baseEnd_1733349] using wordTrace_append hprefix tailTrace_1733349
  have hstable : (prefixWord ++ tailWord_1733349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733349).length < 2 ^ (prefixWord ++ tailWord_1733349).sum := by decide
  have hdescent : baseEnd_1733349 < baseStart_1733349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733366 : List Nat := [5, 1, 1, 1, 1, 2, 4, 6]
def baseStart_1733366 : Nat := 118140960795 + 1733366 * 2 ^ 59
def prefixEnd_1733366 : Nat := 4983230072969 + 3 ^ 40 * 1733366 * 2
def baseEnd_1733366 : Nat := 131859245653536360185689

theorem tailTrace_1733366 : CollatzResearch.WordTrace tailWord_1733366 prefixEnd_1733366 131859245653536360185689 := by
  unfold tailWord_1733366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3951315739894905761833247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42147367892212328126221301 3951315739894905761833247)
  ·
    refine ⟨5926973609842358642749871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3951315739894905761833247 5926973609842358642749871)
    ·
      refine ⟨8890460414763537964124807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5926973609842358642749871 8890460414763537964124807)
      ·
        refine ⟨13335690622145306946187211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8890460414763537964124807 13335690622145306946187211)
        ·
          refine ⟨20003535933217960419280817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13335690622145306946187211 20003535933217960419280817)
          ·
            refine ⟨15002651949913470314460613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20003535933217960419280817 15002651949913470314460613)
            ·
              refine ⟨2812997240608775683961365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15002651949913470314460613 2812997240608775683961365)
              ·
                refine ⟨131859245653536360185689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2812997240608775683961365 131859245653536360185689)
                ·
                  rfl

theorem cell21_1733366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_1733366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733366 prefixEnd_1733366 := by exact prefixLift 1733366
  have htrace : WordTrace (prefixWord ++ tailWord_1733366) baseStart_1733366 baseEnd_1733366 := by
    simpa [prefixWord, tailWord_1733366, baseEnd_1733366] using wordTrace_append hprefix tailTrace_1733366
  have hstable : (prefixWord ++ tailWord_1733366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733366).length < 2 ^ (prefixWord ++ tailWord_1733366).sum := by decide
  have hdescent : baseEnd_1733366 < baseStart_1733366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733380 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_1733380 : Nat := 118140960795 + 1733380 * 2 ^ 59
def prefixEnd_1733380 : Nat := 4983230072969 + 3 ^ 40 * 1733380 * 2
def baseEnd_1733380 : Nat := 395580931951348167323705

theorem tailTrace_1733380 : CollatzResearch.WordTrace tailWord_1733380 prefixEnd_1733380 395580931951348167323705 := by
  unfold tailWord_1733380
  simp only [CollatzResearch.WordTrace]
  refine ⟨31610781230133886290170797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42147708306845181720227729 31610781230133886290170797)
  ·
    refine ⟨11854042961300207358814049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31610781230133886290170797 11854042961300207358814049)
    ·
      refine ⟨8890532220975155519110537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11854042961300207358814049 8890532220975155519110537)
      ·
        refine ⟨6667899165731366639332903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8890532220975155519110537 6667899165731366639332903)
        ·
          refine ⟨10001848748597049958999355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667899165731366639332903 10001848748597049958999355)
          ·
            refine ⟨15002773122895574938499033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10001848748597049958999355 15002773122895574938499033)
            ·
              refine ⟨11252079842171681203874275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15002773122895574938499033 11252079842171681203874275)
              ·
                refine ⟨16878119763257521805811413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11252079842171681203874275 16878119763257521805811413)
                ·
                  refine ⟨395580931951348167323705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16878119763257521805811413 395580931951348167323705)
                  ·
                    rfl

theorem cell21_1733380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_1733380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733380 prefixEnd_1733380 := by exact prefixLift 1733380
  have htrace : WordTrace (prefixWord ++ tailWord_1733380) baseStart_1733380 baseEnd_1733380 := by
    simpa [prefixWord, tailWord_1733380, baseEnd_1733380] using wordTrace_append hprefix tailTrace_1733380
  have hstable : (prefixWord ++ tailWord_1733380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733380).length < 2 ^ (prefixWord ++ tailWord_1733380).sum := by decide
  have hdescent : baseEnd_1733380 < baseStart_1733380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733397 : List Nat := [1, 3, 2, 1, 2, 2, 2, 5, 3]
def baseStart_1733397 : Nat := 118140960795 + 1733397 * 2 ^ 59
def prefixEnd_1733397 : Nat := 4983230072969 + 3 ^ 40 * 1733397 * 2
def baseEnd_1733397 : Nat := 395584811582959915540337

theorem tailTrace_1733397 : CollatzResearch.WordTrace tailWord_1733397 prefixEnd_1733397 395584811582959915540337 := by
  unfold tailWord_1733397
  simp only [CollatzResearch.WordTrace]
  refine ⟨63222182501206184483710445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42148121667470789655806963 63222182501206184483710445)
  ·
    refine ⟨23708318437952319181391417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63222182501206184483710445 23708318437952319181391417)
    ·
      refine ⟨17781238828464239386043563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23708318437952319181391417 17781238828464239386043563)
      ·
        refine ⟨26671858242696359079065345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17781238828464239386043563 26671858242696359079065345)
        ·
          refine ⟨20003893682022269309299009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26671858242696359079065345 20003893682022269309299009)
          ·
            refine ⟨15002920261516701981974257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20003893682022269309299009 15002920261516701981974257)
            ·
              refine ⟨11252190196137526486480693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15002920261516701981974257 11252190196137526486480693)
              ·
                refine ⟨1054892830887893108107565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11252190196137526486480693 1054892830887893108107565)
                ·
                  refine ⟨395584811582959915540337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054892830887893108107565 395584811582959915540337)
                  ·
                    rfl

theorem cell21_1733397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_1733397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733397 prefixEnd_1733397 := by exact prefixLift 1733397
  have htrace : WordTrace (prefixWord ++ tailWord_1733397) baseStart_1733397 baseEnd_1733397 := by
    simpa [prefixWord, tailWord_1733397, baseEnd_1733397] using wordTrace_append hprefix tailTrace_1733397
  have hstable : (prefixWord ++ tailWord_1733397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733397).length < 2 ^ (prefixWord ++ tailWord_1733397).sum := by decide
  have hdescent : baseEnd_1733397 < baseStart_1733397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733515 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 7]
def baseStart_1733515 : Nat := 118140960795 + 1733515 * 2 ^ 59
def prefixEnd_1733515 : Nat := 4983230072969 + 3 ^ 40 * 1733515 * 2
def baseEnd_1733515 : Nat := 395611740790617932573429

theorem tailTrace_1733515 : CollatzResearch.WordTrace tailWord_1733515 prefixEnd_1733515 395611740790617932573429 := by
  unfold tailWord_1733515
  simp only [CollatzResearch.WordTrace]
  refine ⟨63226486314778690636505999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42150990876519127091003999 63226486314778690636505999)
  ·
    refine ⟨94839729472168035954758999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63226486314778690636505999 94839729472168035954758999)
    ·
      refine ⟨142259594208252053932138499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94839729472168035954758999 142259594208252053932138499)
      ·
        refine ⟨213389391312378080898207749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142259594208252053932138499 213389391312378080898207749)
        ·
          refine ⟨40010510871070890168413953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213389391312378080898207749 40010510871070890168413953)
          ·
            refine ⟨30007883153303167626310465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40010510871070890168413953 30007883153303167626310465)
            ·
              refine ⟨22505912364977375719732849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30007883153303167626310465 22505912364977375719732849)
              ·
                refine ⟨16879434273733031789799637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22505912364977375719732849 16879434273733031789799637)
                ·
                  refine ⟨395611740790617932573429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16879434273733031789799637 395611740790617932573429)
                  ·
                    rfl

theorem cell21_1733515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_1733515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733515 prefixEnd_1733515 := by exact prefixLift 1733515
  have htrace : WordTrace (prefixWord ++ tailWord_1733515) baseStart_1733515 baseEnd_1733515 := by
    simpa [prefixWord, tailWord_1733515, baseEnd_1733515] using wordTrace_append hprefix tailTrace_1733515
  have hstable : (prefixWord ++ tailWord_1733515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733515).length < 2 ^ (prefixWord ++ tailWord_1733515).sum := by decide
  have hdescent : baseEnd_1733515 < baseStart_1733515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733594 : List Nat := [3, 1, 1, 2, 4, 3, 1, 6]
def baseStart_1733594 : Nat := 118140960795 + 1733594 * 2 ^ 59
def prefixEnd_1733594 : Nat := 4983230072969 + 3 ^ 40 * 1733594 * 2
def baseEnd_1733594 : Nat := 131876589888977116918867

theorem tailTrace_1733594 : CollatzResearch.WordTrace tailWord_1733594 prefixEnd_1733594 131876589888977116918867 := by
  unfold tailWord_1733594
  simp only [CollatzResearch.WordTrace]
  refine ⟨15807341920373121782157959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42152911787661658085754557 15807341920373121782157959)
  ·
    refine ⟨23711012880559682673236939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15807341920373121782157959 23711012880559682673236939)
    ·
      refine ⟨35566519320839524009855409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23711012880559682673236939 35566519320839524009855409)
      ·
        refine ⟨26674889490629643007391557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35566519320839524009855409 26674889490629643007391557)
        ·
          refine ⟨5001541779493058063885917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26674889490629643007391557 5001541779493058063885917)
          ·
            refine ⟨1875578167309896773957219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5001541779493058063885917 1875578167309896773957219)
            ·
              refine ⟨2813367250964845160935829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875578167309896773957219 2813367250964845160935829)
              ·
                refine ⟨131876589888977116918867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2813367250964845160935829 131876589888977116918867)
                ·
                  rfl

theorem cell21_1733594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_1733594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733594 prefixEnd_1733594 := by exact prefixLift 1733594
  have htrace : WordTrace (prefixWord ++ tailWord_1733594) baseStart_1733594 baseEnd_1733594 := by
    simpa [prefixWord, tailWord_1733594, baseEnd_1733594] using wordTrace_append hprefix tailTrace_1733594
  have hstable : (prefixWord ++ tailWord_1733594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733594).length < 2 ^ (prefixWord ++ tailWord_1733594).sum := by decide
  have hdescent : baseEnd_1733594 < baseStart_1733594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733625 : List Nat := [1, 2, 1, 3, 1, 3, 4, 3, 3]
def baseStart_1733625 : Nat := 118140960795 + 1733625 * 2 ^ 59
def prefixEnd_1733625 : Nat := 4983230072969 + 3 ^ 40 * 1733625 * 2
def baseEnd_1733625 : Nat := 395636844289282185739871

theorem tailTrace_1733625 : CollatzResearch.WordTrace tailWord_1733625 prefixEnd_1733625 395636844289282185739871 := by
  unfold tailWord_1733625
  simp only [CollatzResearch.WordTrace]
  refine ⟨63230498344380179423010329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42153665562920119615340219 63230498344380179423010329)
  ·
    refine ⟨47422873758285134567257747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63230498344380179423010329 47422873758285134567257747)
    ·
      refine ⟨71134310637427701850886621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47422873758285134567257747 71134310637427701850886621)
      ·
        refine ⟨26675366489035388194082483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71134310637427701850886621 26675366489035388194082483)
        ·
          refine ⟨40013049733553082291123725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26675366489035388194082483 40013049733553082291123725)
          ·
            refine ⟨15004893650082405859171397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40013049733553082291123725 15004893650082405859171397)
            ·
              refine ⟨2813417559390451098594637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15004893650082405859171397 2813417559390451098594637)
              ·
                refine ⟨1055031584771419161972989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2813417559390451098594637 1055031584771419161972989)
                ·
                  refine ⟨395636844289282185739871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055031584771419161972989 395636844289282185739871)
                  ·
                    rfl

theorem cell21_1733625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_1733625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733625 prefixEnd_1733625 := by exact prefixLift 1733625
  have htrace : WordTrace (prefixWord ++ tailWord_1733625) baseStart_1733625 baseEnd_1733625 := by
    simpa [prefixWord, tailWord_1733625, baseEnd_1733625] using wordTrace_append hprefix tailTrace_1733625
  have hstable : (prefixWord ++ tailWord_1733625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733625).length < 2 ^ (prefixWord ++ tailWord_1733625).sum := by decide
  have hdescent : baseEnd_1733625 < baseStart_1733625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733656 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_1733656 : Nat := 118140960795 + 1733656 * 2 ^ 59
def prefixEnd_1733656 : Nat := 4983230072969 + 3 ^ 40 * 1733656 * 2
def baseEnd_1733656 : Nat := 395643918911633020723141

theorem tailTrace_1733656 : CollatzResearch.WordTrace tailWord_1733656 prefixEnd_1733656 395643918911633020723141 := by
  unfold tailWord_1733656
  simp only [CollatzResearch.WordTrace]
  refine ⟨31615814503633935858694411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42154419338178581144925881 31615814503633935858694411)
  ·
    refine ⟨47423721755450903788041617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31615814503633935858694411 47423721755450903788041617)
    ·
      refine ⟨35567791316588177841031213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47423721755450903788041617 35567791316588177841031213)
      ·
        refine ⟨13337921743720566690386705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35567791316588177841031213 13337921743720566690386705)
        ·
          refine ⟨10003441307790425017790029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13337921743720566690386705 10003441307790425017790029)
          ·
            refine ⟨3751290490421409381671261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10003441307790425017790029 3751290490421409381671261)
            ·
              refine ⟨1406733933908028518126723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3751290490421409381671261 1406733933908028518126723)
              ·
                refine ⟨2110100900862042777190085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406733933908028518126723 2110100900862042777190085)
                ·
                  refine ⟨395643918911633020723141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110100900862042777190085 395643918911633020723141)
                  ·
                    rfl

theorem cell21_1733656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_1733656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733656 prefixEnd_1733656 := by exact prefixLift 1733656
  have htrace : WordTrace (prefixWord ++ tailWord_1733656) baseStart_1733656 baseEnd_1733656 := by
    simpa [prefixWord, tailWord_1733656, baseEnd_1733656] using wordTrace_append hprefix tailTrace_1733656
  have hstable : (prefixWord ++ tailWord_1733656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733656).length < 2 ^ (prefixWord ++ tailWord_1733656).sum := by decide
  have hdescent : baseEnd_1733656 < baseStart_1733656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733749 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 4]
def baseStart_1733749 : Nat := 118140960795 + 1733749 * 2 ^ 59
def prefixEnd_1733749 : Nat := 4983230072969 + 3 ^ 40 * 1733749 * 2
def baseEnd_1733749 : Nat := 395665142778685525672951

theorem tailTrace_1733749 : CollatzResearch.WordTrace tailWord_1733749 prefixEnd_1733749 395665142778685525672951 := by
  unfold tailWord_1733749
  simp only [CollatzResearch.WordTrace]
  refine ⟨63235020995930948600524301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42156680663953965733682867 63235020995930948600524301)
  ·
    refine ⟨23713132873474105725196613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63235020995930948600524301 23713132873474105725196613)
    ·
      refine ⟨4446212413776394823474365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23713132873474105725196613 4446212413776394823474365)
      ·
        refine ⟨1667329655166148058802887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4446212413776394823474365 1667329655166148058802887)
        ·
          refine ⟨2500994482749222088204331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667329655166148058802887 2500994482749222088204331)
          ·
            refine ⟨3751491724123833132306497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500994482749222088204331 3751491724123833132306497)
            ·
              refine ⟨2813618793092874849229873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3751491724123833132306497 2813618793092874849229873)
              ·
                refine ⟨2110214094819656136922405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2813618793092874849229873 2110214094819656136922405)
                ·
                  refine ⟨395665142778685525672951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110214094819656136922405 395665142778685525672951)
                  ·
                    rfl

theorem cell21_1733749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_1733749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733749 prefixEnd_1733749 := by exact prefixLift 1733749
  have htrace : WordTrace (prefixWord ++ tailWord_1733749) baseStart_1733749 baseEnd_1733749 := by
    simpa [prefixWord, tailWord_1733749, baseEnd_1733749] using wordTrace_append hprefix tailTrace_1733749
  have hstable : (prefixWord ++ tailWord_1733749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733749).length < 2 ^ (prefixWord ++ tailWord_1733749).sum := by decide
  have hdescent : baseEnd_1733749 < baseStart_1733749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733825 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 4]
def baseStart_1733825 : Nat := 118140960795 + 1733825 * 2 ^ 59
def prefixEnd_1733825 : Nat := 4983230072969 + 3 ^ 40 * 1733825 * 2
def baseEnd_1733825 : Nat := 395682487014126282406129

theorem tailTrace_1733825 : CollatzResearch.WordTrace tailWord_1733825 prefixEnd_1733825 395682487014126282406129 := by
  unfold tailWord_1733825
  simp only [CollatzResearch.WordTrace]
  refine ⟨63237792943655613580290929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42158528629103742386860619 63237792943655613580290929)
  ·
    refine ⟨47428344707741710185218197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63237792943655613580290929 47428344707741710185218197)
    ·
      refine ⟨2223203658175392664932103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47428344707741710185218197 2223203658175392664932103)
      ·
        refine ⟨3334805487263088997398155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223203658175392664932103 3334805487263088997398155)
        ·
          refine ⟨5002208230894633496097233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334805487263088997398155 5002208230894633496097233)
          ·
            refine ⟨3751656173170975122072925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5002208230894633496097233 3751656173170975122072925)
            ·
              refine ⟨1406871064939115670777347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3751656173170975122072925 1406871064939115670777347)
              ·
                refine ⟨2110306597408673506166021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406871064939115670777347 2110306597408673506166021)
                ·
                  refine ⟨395682487014126282406129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110306597408673506166021 395682487014126282406129)
                  ·
                    rfl

theorem cell21_1733825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_1733825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733825 prefixEnd_1733825 := by exact prefixLift 1733825
  have htrace : WordTrace (prefixWord ++ tailWord_1733825) baseStart_1733825 baseEnd_1733825 := by
    simpa [prefixWord, tailWord_1733825, baseEnd_1733825] using wordTrace_append hprefix tailTrace_1733825
  have hstable : (prefixWord ++ tailWord_1733825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733825).length < 2 ^ (prefixWord ++ tailWord_1733825).sum := by decide
  have hdescent : baseEnd_1733825 < baseStart_1733825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733876 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1733876 : Nat := 118140960795 + 1733876 * 2 ^ 59
def prefixEnd_1733876 : Nat := 4983230072969 + 3 ^ 40 * 1733876 * 2
def baseEnd_1733876 : Nat := 395694125908961527056025

theorem tailTrace_1733876 : CollatzResearch.WordTrace tailWord_1733876 prefixEnd_1733876 395694125908961527056025 := by
  unfold tailWord_1733876
  simp only [CollatzResearch.WordTrace]
  refine ⟨31619826533235424645198741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42159768710980566193598321 31619826533235424645198741)
  ·
    refine ⟨1482179368745410530243691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31619826533235424645198741 1482179368745410530243691)
    ·
      refine ⟨2223269053118115795365537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1482179368745410530243691 2223269053118115795365537)
      ·
        refine ⟨1667451789838586846524153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2223269053118115795365537 1667451789838586846524153)
        ·
          refine ⟨1250588842378940134893115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1667451789838586846524153 1250588842378940134893115)
          ·
            refine ⟨1875883263568410202339673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250588842378940134893115 1875883263568410202339673)
            ·
              refine ⟨1406912447676307651754755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875883263568410202339673 1406912447676307651754755)
              ·
                refine ⟨2110368671514461477632133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406912447676307651754755 2110368671514461477632133)
                ·
                  refine ⟨395694125908961527056025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110368671514461477632133 395694125908961527056025)
                  ·
                    rfl

theorem cell21_1733876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1733876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733876 prefixEnd_1733876 := by exact prefixLift 1733876
  have htrace : WordTrace (prefixWord ++ tailWord_1733876) baseStart_1733876 baseEnd_1733876 := by
    simpa [prefixWord, tailWord_1733876, baseEnd_1733876] using wordTrace_append hprefix tailTrace_1733876
  have hstable : (prefixWord ++ tailWord_1733876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733876).length < 2 ^ (prefixWord ++ tailWord_1733876).sum := by decide
  have hdescent : baseEnd_1733876 < baseStart_1733876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1733988 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1733988 : Nat := 118140960795 + 1733988 * 2 ^ 59
def prefixEnd_1733988 : Nat := 4983230072969 + 3 ^ 40 * 1733988 * 2
def baseEnd_1733988 : Nat := 395719685834874221189129

theorem tailTrace_1733988 : CollatzResearch.WordTrace tailWord_1733988 prefixEnd_1733988 395719685834874221189129 := by
  unfold tailWord_1733988
  simp only [CollatzResearch.WordTrace]
  refine ⟨31621869021032546209237309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42162492028043394945649745 31621869021032546209237309)
  ·
    refine ⟨11858200882887204828463991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31621869021032546209237309 11858200882887204828463991)
    ·
      refine ⟨17787301324330807242695987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11858200882887204828463991 17787301324330807242695987)
      ·
        refine ⟨26680951986496210864043981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17787301324330807242695987 26680951986496210864043981)
        ·
          refine ⟨10005356994936079074016493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26680951986496210864043981 10005356994936079074016493)
          ·
            refine ⟨3752008873101029652756185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10005356994936079074016493 3752008873101029652756185)
            ·
              refine ⟨2814006654825772239567139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752008873101029652756185 2814006654825772239567139)
              ·
                refine ⟨4221009982238658359350709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814006654825772239567139 4221009982238658359350709)
                ·
                  refine ⟨395719685834874221189129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4221009982238658359350709 395719685834874221189129)
                  ·
                    rfl

theorem cell21_1733988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1733988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1733988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1733988 prefixEnd_1733988 := by exact prefixLift 1733988
  have htrace : WordTrace (prefixWord ++ tailWord_1733988) baseStart_1733988 baseEnd_1733988 := by
    simpa [prefixWord, tailWord_1733988, baseEnd_1733988] using wordTrace_append hprefix tailTrace_1733988
  have hstable : (prefixWord ++ tailWord_1733988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1733988).length < 2 ^ (prefixWord ++ tailWord_1733988).sum := by decide
  have hdescent : baseEnd_1733988 < baseStart_1733988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1733988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734092 : List Nat := [2, 2, 1, 4, 2, 10]
def baseStart_1734092 : Nat := 118140960795 + 1734092 * 2 ^ 59
def prefixEnd_1734092 : Nat := 4983230072969 + 3 ^ 40 * 1734092 * 2
def baseEnd_1734092 : Nat := 14657163705621968572429

theorem tailTrace_1734092 : CollatzResearch.WordTrace tailWord_1734092 prefixEnd_1734092 14657163705621968572429 := by
  unfold tailWord_1734092
  simp only [CollatzResearch.WordTrace]
  refine ⟨31623765616844159090130265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42165020822458878786840353 31623765616844159090130265)
  ·
    refine ⟨23717824212633119317597699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31623765616844159090130265 23717824212633119317597699)
    ·
      refine ⟨35576736318949678976396549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23717824212633119317597699 35576736318949678976396549)
      ·
        refine ⟨6670638059803064808074353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35576736318949678976396549 6670638059803064808074353)
        ·
          refine ⟨5002978544852298606055765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6670638059803064808074353 5002978544852298606055765)
          ·
            refine ⟨14657163705621968572429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5002978544852298606055765 14657163705621968572429)
            ·
              rfl

theorem cell21_1734092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 10].length) (baseStart_1734092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734092 prefixEnd_1734092 := by exact prefixLift 1734092
  have htrace : WordTrace (prefixWord ++ tailWord_1734092) baseStart_1734092 baseEnd_1734092 := by
    simpa [prefixWord, tailWord_1734092, baseEnd_1734092] using wordTrace_append hprefix tailTrace_1734092
  have hstable : (prefixWord ++ tailWord_1734092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734092).length < 2 ^ (prefixWord ++ tailWord_1734092).sum := by decide
  have hdescent : baseEnd_1734092 < baseStart_1734092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734109 : List Nat := [1, 4, 3, 1, 1, 2, 3, 6]
def baseStart_1734109 : Nat := 118140960795 + 1734109 * 2 ^ 59
def prefixEnd_1734109 : Nat := 4983230072969 + 3 ^ 40 * 1734109 * 2
def baseEnd_1734109 : Nat := 131915766561134966557405

theorem tailTrace_1734109 : CollatzResearch.WordTrace tailWord_1734109 prefixEnd_1734109 131915766561134966557405 := by
  unfold tailWord_1734109
  simp only [CollatzResearch.WordTrace]
  refine ⟨63248151274626730083629381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42165434183084486722419587 63248151274626730083629381)
  ·
    refine ⟨11859028363992511890680509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63248151274626730083629381 11859028363992511890680509)
    ·
      refine ⟨4447135636497191959005191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11859028363992511890680509 4447135636497191959005191)
      ·
        refine ⟨6670703454745787938507787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447135636497191959005191 6670703454745787938507787)
        ·
          refine ⟨10006055182118681907761681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6670703454745787938507787 10006055182118681907761681)
          ·
            refine ⟨7504541386589011430821261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10006055182118681907761681 7504541386589011430821261)
            ·
              refine ⟨2814203019970879286557973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7504541386589011430821261 2814203019970879286557973)
              ·
                refine ⟨131915766561134966557405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2814203019970879286557973 131915766561134966557405)
                ·
                  rfl

theorem cell21_1734109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 6].length) (baseStart_1734109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734109 prefixEnd_1734109 := by exact prefixLift 1734109
  have htrace : WordTrace (prefixWord ++ tailWord_1734109) baseStart_1734109 baseEnd_1734109 := by
    simpa [prefixWord, tailWord_1734109, baseEnd_1734109] using wordTrace_append hprefix tailTrace_1734109
  have hstable : (prefixWord ++ tailWord_1734109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734109).length < 2 ^ (prefixWord ++ tailWord_1734109).sum := by decide
  have hdescent : baseEnd_1734109 < baseStart_1734109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734137 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 6]
def baseStart_1734137 : Nat := 118140960795 + 1734137 * 2 ^ 59
def prefixEnd_1734137 : Nat := 4983230072969 + 3 ^ 40 * 1734137 * 2
def baseEnd_1734137 : Nat := 395753689664883073205491

theorem tailTrace_1734137 : CollatzResearch.WordTrace tailWord_1734137 prefixEnd_1734137 395753689664883073205491 := by
  unfold tailWord_1734137
  simp only [CollatzResearch.WordTrace]
  refine ⟨63249172518525290865648665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42166115012350193910432443 63249172518525290865648665)
  ·
    refine ⟨47436879388893968149236499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63249172518525290865648665 47436879388893968149236499)
    ·
      refine ⟨71155319083340952223854749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47436879388893968149236499 71155319083340952223854749)
      ·
        refine ⟨26683244656252857083945531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71155319083340952223854749 26683244656252857083945531)
        ·
          refine ⟨40024866984379285625918297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26683244656252857083945531 40024866984379285625918297)
          ·
            refine ⟨30018650238284464219438723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40024866984379285625918297 30018650238284464219438723)
            ·
              refine ⟨45027975357426696329158085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30018650238284464219438723 45027975357426696329158085)
              ·
                refine ⟨8442745379517505561717141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45027975357426696329158085 8442745379517505561717141)
                ·
                  refine ⟨395753689664883073205491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8442745379517505561717141 395753689664883073205491)
                  ·
                    rfl

theorem cell21_1734137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_1734137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734137 prefixEnd_1734137 := by exact prefixLift 1734137
  have htrace : WordTrace (prefixWord ++ tailWord_1734137) baseStart_1734137 baseEnd_1734137 := by
    simpa [prefixWord, tailWord_1734137, baseEnd_1734137] using wordTrace_append hprefix tailTrace_1734137
  have hstable : (prefixWord ++ tailWord_1734137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734137).length < 2 ^ (prefixWord ++ tailWord_1734137).sum := by decide
  have hdescent : baseEnd_1734137 < baseStart_1734137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734140 : List Nat := [2, 2, 2, 1, 2, 1, 3, 5, 3]
def baseStart_1734140 : Nat := 118140960795 + 1734140 * 2 ^ 59
def prefixEnd_1734140 : Nat := 4983230072969 + 3 ^ 40 * 1734140 * 2
def baseEnd_1734140 : Nat := 395754374305755734655485

theorem tailTrace_1734140 : CollatzResearch.WordTrace tailWord_1734140 prefixEnd_1734140 395754374305755734655485 := by
  unfold tailWord_1734140
  simp only [CollatzResearch.WordTrace]
  refine ⟨31624640968757211189003937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42166187958342948252005249 31624640968757211189003937)
  ·
    refine ⟨23718480726567908391752953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31624640968757211189003937 23718480726567908391752953)
    ·
      refine ⟨17788860544925931293814715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23718480726567908391752953 17788860544925931293814715)
      ·
        refine ⟨26683290817388896940722073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17788860544925931293814715 26683290817388896940722073)
        ·
          refine ⟨20012468113041672705541555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26683290817388896940722073 20012468113041672705541555)
          ·
            refine ⟨30018702169562509058312333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20012468113041672705541555 30018702169562509058312333)
            ·
              refine ⟨11257013313585940896867125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30018702169562509058312333 11257013313585940896867125)
              ·
                refine ⟨1055344998148681959081293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11257013313585940896867125 1055344998148681959081293)
                ·
                  refine ⟨395754374305755734655485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055344998148681959081293 395754374305755734655485)
                  ·
                    rfl

theorem cell21_1734140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_1734140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734140 prefixEnd_1734140 := by exact prefixLift 1734140
  have htrace : WordTrace (prefixWord ++ tailWord_1734140) baseStart_1734140 baseEnd_1734140 := by
    simpa [prefixWord, tailWord_1734140, baseEnd_1734140] using wordTrace_append hprefix tailTrace_1734140
  have hstable : (prefixWord ++ tailWord_1734140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734140).length < 2 ^ (prefixWord ++ tailWord_1734140).sum := by decide
  have hdescent : baseEnd_1734140 < baseStart_1734140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734154 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_1734154 : Nat := 118140960795 + 1734154 * 2 ^ 59
def prefixEnd_1734154 : Nat := 4983230072969 + 3 ^ 40 * 1734154 * 2
def baseEnd_1734154 : Nat := 395757569296494821422123

theorem tailTrace_1734154 : CollatzResearch.WordTrace tailWord_1734154 prefixEnd_1734154 395757569296494821422123 := by
  unfold tailWord_1734154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15812448139865925692254379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42166528372975801846011677 15812448139865925692254379)
  ·
    refine ⟨23718672209798888538381569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15812448139865925692254379 23718672209798888538381569)
    ·
      refine ⟨17789004157349166403786177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23718672209798888538381569 17789004157349166403786177)
      ·
        refine ⟨13341753118011874802839633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17789004157349166403786177 13341753118011874802839633)
        ·
          refine ⟨10006314838508906102129725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13341753118011874802839633 10006314838508906102129725)
          ·
            refine ⟨3752368064440839788298647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10006314838508906102129725 3752368064440839788298647)
            ·
              refine ⟨5628552096661259682447971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752368064440839788298647 5628552096661259682447971)
              ·
                refine ⟨8442828144991889523671957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628552096661259682447971 8442828144991889523671957)
                ·
                  refine ⟨395757569296494821422123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8442828144991889523671957 395757569296494821422123)
                  ·
                    rfl

theorem cell21_1734154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_1734154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734154 prefixEnd_1734154 := by exact prefixLift 1734154
  have htrace : WordTrace (prefixWord ++ tailWord_1734154) baseStart_1734154 baseEnd_1734154 := by
    simpa [prefixWord, tailWord_1734154, baseEnd_1734154] using wordTrace_append hprefix tailTrace_1734154
  have hstable : (prefixWord ++ tailWord_1734154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734154).length < 2 ^ (prefixWord ++ tailWord_1734154).sum := by decide
  have hdescent : baseEnd_1734154 < baseStart_1734154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734213 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 6]
def baseStart_1734213 : Nat := 118140960795 + 1734213 * 2 ^ 59
def prefixEnd_1734213 : Nat := 4983230072969 + 3 ^ 40 * 1734213 * 2
def baseEnd_1734213 : Nat := 395771033900323829938669

theorem tailTrace_1734213 : CollatzResearch.WordTrace tailWord_1734213 prefixEnd_1734213 395771033900323829938669 := by
  unfold tailWord_1734213
  simp only [CollatzResearch.WordTrace]
  refine ⟨63251944466249955845415293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42167962977499970563610195 63251944466249955845415293)
  ·
    refine ⟨23719479174843733442030735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63251944466249955845415293 23719479174843733442030735)
    ·
      refine ⟨35579218762265600163046103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23719479174843733442030735 35579218762265600163046103)
      ·
        refine ⟨53368828143398400244569155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35579218762265600163046103 53368828143398400244569155)
        ·
          refine ⟨80053242215097600366853733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53368828143398400244569155 80053242215097600366853733)
          ·
            refine ⟨15009982915330800068785075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80053242215097600366853733 15009982915330800068785075)
            ·
              refine ⟨22514974372996200103177613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15009982915330800068785075 22514974372996200103177613)
              ·
                refine ⟨8443115389873575038691605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22514974372996200103177613 8443115389873575038691605)
                ·
                  refine ⟨395771033900323829938669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8443115389873575038691605 395771033900323829938669)
                  ·
                    rfl

theorem cell21_1734213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_1734213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734213 prefixEnd_1734213 := by exact prefixLift 1734213
  have htrace : WordTrace (prefixWord ++ tailWord_1734213) baseStart_1734213 baseEnd_1734213 := by
    simpa [prefixWord, tailWord_1734213, baseEnd_1734213] using wordTrace_append hprefix tailTrace_1734213
  have hstable : (prefixWord ++ tailWord_1734213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734213).length < 2 ^ (prefixWord ++ tailWord_1734213).sum := by decide
  have hdescent : baseEnd_1734213 < baseStart_1734213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734244 : List Nat := [2, 3, 1, 1, 2, 3, 2, 7]
def baseStart_1734244 : Nat := 118140960795 + 1734244 * 2 ^ 59
def prefixEnd_1734244 : Nat := 4983230072969 + 3 ^ 40 * 1734244 * 2
def baseEnd_1734244 : Nat := 131926036174224888307313

theorem tailTrace_1734244 : CollatzResearch.WordTrace tailWord_1734244 prefixEnd_1734244 131926036174224888307313 := by
  unfold tailWord_1734244
  simp only [CollatzResearch.WordTrace]
  refine ⟨31626537564568824069896893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42168716752758432093195857 31626537564568824069896893)
  ·
    refine ⟨11859951586713309026211335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31626537564568824069896893 11859951586713309026211335)
    ·
      refine ⟨17789927380069963539317003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11859951586713309026211335 17789927380069963539317003)
      ·
        refine ⟨26684891070104945308975505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17789927380069963539317003 26684891070104945308975505)
        ·
          refine ⟨20013668302578708981731629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26684891070104945308975505 20013668302578708981731629)
          ·
            refine ⟨7505125613467015868149361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20013668302578708981731629 7505125613467015868149361)
            ·
              refine ⟨5628844210100261901112021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7505125613467015868149361 5628844210100261901112021)
              ·
                refine ⟨131926036174224888307313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5628844210100261901112021 131926036174224888307313)
                ·
                  rfl

theorem cell21_1734244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_1734244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734244 prefixEnd_1734244 := by exact prefixLift 1734244
  have htrace : WordTrace (prefixWord ++ tailWord_1734244) baseStart_1734244 baseEnd_1734244 := by
    simpa [prefixWord, tailWord_1734244, baseEnd_1734244] using wordTrace_append hprefix tailTrace_1734244
  have hstable : (prefixWord ++ tailWord_1734244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734244).length < 2 ^ (prefixWord ++ tailWord_1734244).sum := by decide
  have hdescent : baseEnd_1734244 < baseStart_1734244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734326 : List Nat := [5, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1734326 : Nat := 118140960795 + 1734326 * 2 ^ 59
def prefixEnd_1734326 : Nat := 4983230072969 + 3 ^ 40 * 1734326 * 2
def baseEnd_1734326 : Nat := 395796822039860744555105

theorem tailTrace_1734326 : CollatzResearch.WordTrace tailWord_1734326 prefixEnd_1734326 395796822039860744555105 := by
  unfold tailWord_1734326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3953504119677536009017427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42170710609893717429519221 3953504119677536009017427)
  ·
    refine ⟨5930256179516304013526141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3953504119677536009017427 5930256179516304013526141)
    ·
      refine ⟨2223846067318614005072303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5930256179516304013526141 2223846067318614005072303)
      ·
        refine ⟨3335769100977921007608455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223846067318614005072303 3335769100977921007608455)
        ·
          refine ⟨5003653651466881511412683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335769100977921007608455 5003653651466881511412683)
          ·
            refine ⟨7505480477200322267119025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003653651466881511412683 7505480477200322267119025)
            ·
              refine ⟨5629110357900241700339269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7505480477200322267119025 5629110357900241700339269)
              ·
                refine ⟨1055458192106295318813613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5629110357900241700339269 1055458192106295318813613)
                ·
                  refine ⟨395796822039860744555105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055458192106295318813613 395796822039860744555105)
                  ·
                    rfl

theorem cell21_1734326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1734326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734326 prefixEnd_1734326 := by exact prefixLift 1734326
  have htrace : WordTrace (prefixWord ++ tailWord_1734326) baseStart_1734326 baseEnd_1734326 := by
    simpa [prefixWord, tailWord_1734326, baseEnd_1734326] using wordTrace_append hprefix tailTrace_1734326
  have hstable : (prefixWord ++ tailWord_1734326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734326).length < 2 ^ (prefixWord ++ tailWord_1734326).sum := by decide
  have hdescent : baseEnd_1734326 < baseStart_1734326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734354 : List Nat := [3, 2, 2, 2, 2, 3, 2, 5]
def baseStart_1734354 : Nat := 118140960795 + 1734354 * 2 ^ 59
def prefixEnd_1734354 : Nat := 4983230072969 + 3 ^ 40 * 1734354 * 2
def baseEnd_1734354 : Nat := 131934404007112972696127

theorem tailTrace_1734354 : CollatzResearch.WordTrace tailWord_1734354 prefixEnd_1734354 131934404007112972696127 := by
  unfold tailWord_1734354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814271789684784231574529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42171391439159424617532077 15814271789684784231574529)
  ·
    refine ⟨11860703842263588173680897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15814271789684784231574529 11860703842263588173680897)
    ·
      refine ⟨8895527881697691130260673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11860703842263588173680897 8895527881697691130260673)
      ·
        refine ⟨6671645911273268347695505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8895527881697691130260673 6671645911273268347695505)
        ·
          refine ⟨5003734433454951260771629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6671645911273268347695505 5003734433454951260771629)
          ·
            refine ⟨1876400412545606722789361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5003734433454951260771629 1876400412545606722789361)
            ·
              refine ⟨1407300309409205042092021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1876400412545606722789361 1407300309409205042092021)
              ·
                refine ⟨131934404007112972696127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1407300309409205042092021 131934404007112972696127)
                ·
                  rfl

theorem cell21_1734354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_1734354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734354 prefixEnd_1734354 := by exact prefixLift 1734354
  have htrace : WordTrace (prefixWord ++ tailWord_1734354) baseStart_1734354 baseEnd_1734354 := by
    simpa [prefixWord, tailWord_1734354, baseEnd_1734354] using wordTrace_append hprefix tailTrace_1734354
  have hstable : (prefixWord ++ tailWord_1734354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734354).length < 2 ^ (prefixWord ++ tailWord_1734354).sum := by decide
  have hdescent : baseEnd_1734354 < baseStart_1734354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734368 : List Nat := [2, 1, 1, 3, 1, 2, 5, 3, 3]
def baseStart_1734368 : Nat := 118140960795 + 1734368 * 2 ^ 59
def prefixEnd_1734368 : Nat := 4983230072969 + 3 ^ 40 * 1734368 * 2
def baseEnd_1734368 : Nat := 395806407012078004855019

theorem tailTrace_1734368 : CollatzResearch.WordTrace tailWord_1734368 prefixEnd_1734368 395806407012078004855019 := by
  unfold tailWord_1734368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31628798890344208658653879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42171731853792278211538505 31628798890344208658653879)
  ·
    refine ⟨47443198335516312987980819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31628798890344208658653879 47443198335516312987980819)
    ·
      refine ⟨71164797503274469481971229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47443198335516312987980819 71164797503274469481971229)
      ·
        refine ⟨26686799063727926055739211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71164797503274469481971229 26686799063727926055739211)
        ·
          refine ⟨40030198595591889083608817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26686799063727926055739211 40030198595591889083608817)
          ·
            refine ⟨30022648946693916812706613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40030198595591889083608817 30022648946693916812706613)
            ·
              refine ⟨2814623338752554701191245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30022648946693916812706613 2814623338752554701191245)
              ·
                refine ⟨1055483752032208012946717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2814623338752554701191245 1055483752032208012946717)
                ·
                  refine ⟨395806407012078004855019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055483752032208012946717 395806407012078004855019)
                  ·
                    rfl

theorem cell21_1734368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_1734368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734368 prefixEnd_1734368 := by exact prefixLift 1734368
  have htrace : WordTrace (prefixWord ++ tailWord_1734368) baseStart_1734368 baseEnd_1734368 := by
    simpa [prefixWord, tailWord_1734368, baseEnd_1734368] using wordTrace_append hprefix tailTrace_1734368
  have hstable : (prefixWord ++ tailWord_1734368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734368).length < 2 ^ (prefixWord ++ tailWord_1734368).sum := by decide
  have hdescent : baseEnd_1734368 < baseStart_1734368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734379 : List Nat := [1, 1, 1, 1, 2, 4, 11]
def baseStart_1734379 : Nat := 118140960795 + 1734379 * 2 ^ 59
def prefixEnd_1734379 : Nat := 4983230072969 + 3 ^ 40 * 1734379 * 2
def baseEnd_1734379 : Nat := 43978768595771603352407

theorem tailTrace_1734379 : CollatzResearch.WordTrace tailWord_1734379 prefixEnd_1734379 43978768595771603352407 := by
  unfold tailWord_1734379
  simp only [CollatzResearch.WordTrace]
  refine ⟨63257998983648566195958191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42171999322432377463972127 63257998983648566195958191)
  ·
    refine ⟨94886998475472849293937287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63257998983648566195958191 94886998475472849293937287)
    ·
      refine ⟨142330497713209273940905931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94886998475472849293937287 142330497713209273940905931)
      ·
        refine ⟨213495746569813910911358897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142330497713209273940905931 213495746569813910911358897)
        ·
          refine ⟨160121809927360433183519173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213495746569813910911358897 160121809927360433183519173)
          ·
            refine ⟨30022839361380081221909845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160121809927360433183519173 30022839361380081221909845)
            ·
              refine ⟨43978768595771603352407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30022839361380081221909845 43978768595771603352407)
              ·
                rfl

theorem cell21_1734379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 11].length) (baseStart_1734379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734379 prefixEnd_1734379 := by exact prefixLift 1734379
  have htrace : WordTrace (prefixWord ++ tailWord_1734379) baseStart_1734379 baseEnd_1734379 := by
    simpa [prefixWord, tailWord_1734379, baseEnd_1734379] using wordTrace_append hprefix tailTrace_1734379
  have hstable : (prefixWord ++ tailWord_1734379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734379).length < 2 ^ (prefixWord ++ tailWord_1734379).sum := by decide
  have hdescent : baseEnd_1734379 < baseStart_1734379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734382 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_1734382 : Nat := 118140960795 + 1734382 * 2 ^ 59
def prefixEnd_1734382 : Nat := 4983230072969 + 3 ^ 40 * 1734382 * 2
def baseEnd_1734382 : Nat := 395809602002817091621657

theorem tailTrace_1734382 : CollatzResearch.WordTrace tailWord_1734382 prefixEnd_1734382 395809602002817091621657 := by
  unfold tailWord_1734382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907263550329712213539675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42172072268425131805544933 7907263550329712213539675)
  ·
    refine ⟨11860895325494568320309513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7907263550329712213539675 11860895325494568320309513)
    ·
      refine ⟨8895671494120926240232135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11860895325494568320309513 8895671494120926240232135)
      ·
        refine ⟨13343507241181389360348203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8895671494120926240232135 13343507241181389360348203)
        ·
          refine ⟨20015260861772084040522305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13343507241181389360348203 20015260861772084040522305)
          ·
            refine ⟨15011445646329063030391729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20015260861772084040522305 15011445646329063030391729)
            ·
              refine ⟨11258584234746797272793797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15011445646329063030391729 11258584234746797272793797)
              ·
                refine ⟨2110984544015024488648837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11258584234746797272793797 2110984544015024488648837)
                ·
                  refine ⟨395809602002817091621657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110984544015024488648837 395809602002817091621657)
                  ·
                    rfl

theorem cell21_1734382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_1734382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734382 prefixEnd_1734382 := by exact prefixLift 1734382
  have htrace : WordTrace (prefixWord ++ tailWord_1734382) baseStart_1734382 baseEnd_1734382 := by
    simpa [prefixWord, tailWord_1734382, baseEnd_1734382] using wordTrace_append hprefix tailTrace_1734382
  have hstable : (prefixWord ++ tailWord_1734382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734382).length < 2 ^ (prefixWord ++ tailWord_1734382).sum := by decide
  have hdescent : baseEnd_1734382 < baseStart_1734382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734385 : List Nat := [1, 2, 2, 2, 2, 4, 3, 2, 3]
def baseStart_1734385 : Nat := 118140960795 + 1734385 * 2 ^ 59
def prefixEnd_1734385 : Nat := 4983230072969 + 3 ^ 40 * 1734385 * 2
def baseEnd_1734385 : Nat := 395810286643689753071651

theorem tailTrace_1734385 : CollatzResearch.WordTrace tailWord_1734385 prefixEnd_1734385 395810286643689753071651 := by
  unfold tailWord_1734385
  simp only [CollatzResearch.WordTrace]
  refine ⟨63258217821626829220676609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42172145214417886147117739 63258217821626829220676609)
  ·
    refine ⟨47443663366220121915507457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63258217821626829220676609 47443663366220121915507457)
    ·
      refine ⟨35582747524665091436630593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47443663366220121915507457 35582747524665091436630593)
      ·
        refine ⟨26687060643498818577472945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35582747524665091436630593 26687060643498818577472945)
        ·
          refine ⟨20015295482624113933104709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26687060643498818577472945 20015295482624113933104709)
          ·
            refine ⟨3752867902992021362457133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20015295482624113933104709 3752867902992021362457133)
            ·
              refine ⟨1407325463622008010921425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3752867902992021362457133 1407325463622008010921425)
              ·
                refine ⟨1055494097716506008191069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407325463622008010921425 1055494097716506008191069)
                ·
                  refine ⟨395810286643689753071651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055494097716506008191069 395810286643689753071651)
                  ·
                    rfl

theorem cell21_1734385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_1734385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734385 prefixEnd_1734385 := by exact prefixLift 1734385
  have htrace : WordTrace (prefixWord ++ tailWord_1734385) baseStart_1734385 baseEnd_1734385 := by
    simpa [prefixWord, tailWord_1734385, baseEnd_1734385] using wordTrace_append hprefix tailTrace_1734385
  have hstable : (prefixWord ++ tailWord_1734385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734385).length < 2 ^ (prefixWord ++ tailWord_1734385).sum := by decide
  have hdescent : baseEnd_1734385 < baseStart_1734385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734396 : List Nat := [2, 2, 2, 1, 3, 1, 4, 6]
def baseStart_1734396 : Nat := 118140960795 + 1734396 * 2 ^ 59
def prefixEnd_1734396 : Nat := 4983230072969 + 3 ^ 40 * 1734396 * 2
def baseEnd_1734396 : Nat := 131937598997852059462765

theorem tailTrace_1734396 : CollatzResearch.WordTrace tailWord_1734396 prefixEnd_1734396 131937598997852059462765 := by
  unfold tailWord_1734396
  simp only [CollatzResearch.WordTrace]
  refine ⟨31629309512293489049663521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42172412683057985399551361 31629309512293489049663521)
  ·
    refine ⟨23721982134220116787247641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31629309512293489049663521 23721982134220116787247641)
    ·
      refine ⟨17791486600665087590435731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23721982134220116787247641 17791486600665087590435731)
      ·
        refine ⟨26687229900997631385653597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17791486600665087590435731 26687229900997631385653597)
        ·
          refine ⟨10007711212874111769620099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26687229900997631385653597 10007711212874111769620099)
          ·
            refine ⟨15011566819311167654430149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10007711212874111769620099 15011566819311167654430149)
            ·
              refine ⟨2814668778620843935205653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15011566819311167654430149 2814668778620843935205653)
              ·
                refine ⟨131937598997852059462765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2814668778620843935205653 131937598997852059462765)
                ·
                  rfl

theorem cell21_1734396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_1734396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734396 prefixEnd_1734396 := by exact prefixLift 1734396
  have htrace : WordTrace (prefixWord ++ tailWord_1734396) baseStart_1734396 baseEnd_1734396 := by
    simpa [prefixWord, tailWord_1734396, baseEnd_1734396] using wordTrace_append hprefix tailTrace_1734396
  have hstable : (prefixWord ++ tailWord_1734396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734396).length < 2 ^ (prefixWord ++ tailWord_1734396).sum := by decide
  have hdescent : baseEnd_1734396 < baseStart_1734396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734430 : List Nat := [4, 3, 2, 2, 1, 9]
def baseStart_1734430 : Nat := 118140960795 + 1734430 * 2 ^ 59
def prefixEnd_1734430 : Nat := 4983230072969 + 3 ^ 40 * 1734430 * 2
def baseEnd_1734430 : Nat := 14660020602102950919317

theorem tailTrace_1734430 : CollatzResearch.WordTrace tailWord_1734430 prefixEnd_1734430 14660020602102950919317 := by
  unfold tailWord_1734430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907482388307975238258093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42173239404309201270709829 7907482388307975238258093)
  ·
    refine ⟨2965305895615490714346785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7907482388307975238258093 2965305895615490714346785)
    ·
      refine ⟨2223979421711618035760089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2965305895615490714346785 2223979421711618035760089)
      ·
        refine ⟨1667984566283713526820067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2223979421711618035760089 1667984566283713526820067)
        ·
          refine ⟨2501976849425570290230101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667984566283713526820067 2501976849425570290230101)
          ·
            refine ⟨14660020602102950919317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2501976849425570290230101 14660020602102950919317)
            ·
              rfl

theorem cell21_1734430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 9].length) (baseStart_1734430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734430 prefixEnd_1734430 := by exact prefixLift 1734430
  have htrace : WordTrace (prefixWord ++ tailWord_1734430) baseStart_1734430 baseEnd_1734430 := by
    simpa [prefixWord, tailWord_1734430, baseEnd_1734430] using wordTrace_append hprefix tailTrace_1734430
  have hstable : (prefixWord ++ tailWord_1734430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734430).length < 2 ^ (prefixWord ++ tailWord_1734430).sum := by decide
  have hdescent : baseEnd_1734430 < baseStart_1734430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734444 : List Nat := [2, 2, 1, 1, 1, 6, 1, 4, 3]
def baseStart_1734444 : Nat := 118140960795 + 1734444 * 2 ^ 59
def prefixEnd_1734444 : Nat := 4983230072969 + 3 ^ 40 * 1734444 * 2
def baseEnd_1734444 : Nat := 395823751247518761588197

theorem tailTrace_1734444 : CollatzResearch.WordTrace tailWord_1734444 prefixEnd_1734444 395823751247518761588197 := by
  unfold tailWord_1734444
  simp only [CollatzResearch.WordTrace]
  refine ⟨31630184864206541148537193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42173579818942054864716257 31630184864206541148537193)
  ·
    refine ⟨23722638648154905861402895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31630184864206541148537193 23722638648154905861402895)
    ·
      refine ⟨35583957972232358792104343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23722638648154905861402895 35583957972232358792104343)
      ·
        refine ⟨53375936958348538188156515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35583957972232358792104343 53375936958348538188156515)
        ·
          refine ⟨80063905437522807282234773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53375936958348538188156515 80063905437522807282234773)
          ·
            refine ⟨3752995567383881591354755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80063905437522807282234773 3752995567383881591354755)
            ·
              refine ⟨5629493351075822387032133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752995567383881591354755 5629493351075822387032133)
              ·
                refine ⟨1055530003326716697568525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5629493351075822387032133 1055530003326716697568525)
                ·
                  refine ⟨395823751247518761588197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055530003326716697568525 395823751247518761588197)
                  ·
                    rfl

theorem cell21_1734444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_1734444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734444 prefixEnd_1734444 := by exact prefixLift 1734444
  have htrace : WordTrace (prefixWord ++ tailWord_1734444) baseStart_1734444 baseEnd_1734444 := by
    simpa [prefixWord, tailWord_1734444, baseEnd_1734444] using wordTrace_append hprefix tailTrace_1734444
  have hstable : (prefixWord ++ tailWord_1734444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734444).length < 2 ^ (prefixWord ++ tailWord_1734444).sum := by decide
  have hdescent : baseEnd_1734444 < baseStart_1734444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734455 : List Nat := [1, 1, 3, 1, 2, 1, 2, 10]
def baseStart_1734455 : Nat := 118140960795 + 1734455 * 2 ^ 59
def prefixEnd_1734455 : Nat := 4983230072969 + 3 ^ 40 * 1734455 * 2
def baseEnd_1734455 : Nat := 131942087199128395634947

theorem tailTrace_1734455 : CollatzResearch.WordTrace tailWord_1734455 prefixEnd_1734455 131942087199128395634947 := by
  unfold tailWord_1734455
  simp only [CollatzResearch.WordTrace]
  refine ⟨63260770931373231175724819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42173847287582154117149879 63260770931373231175724819)
  ·
    refine ⟨94891156397059846763587229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63260770931373231175724819 94891156397059846763587229)
    ·
      refine ⟨35584183648897442536345211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94891156397059846763587229 35584183648897442536345211)
      ·
        refine ⟨53376275473346163804517817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35584183648897442536345211 53376275473346163804517817)
        ·
          refine ⟨40032206605009622853388363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53376275473346163804517817 40032206605009622853388363)
          ·
            refine ⟨60048309907514434280082545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40032206605009622853388363 60048309907514434280082545)
            ·
              refine ⟨45036232430635825710061909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60048309907514434280082545 45036232430635825710061909)
              ·
                refine ⟨131942087199128395634947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45036232430635825710061909 131942087199128395634947)
                ·
                  rfl

theorem cell21_1734455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 10].length) (baseStart_1734455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734455 prefixEnd_1734455 := by exact prefixLift 1734455
  have htrace : WordTrace (prefixWord ++ tailWord_1734455) baseStart_1734455 baseEnd_1734455 := by
    simpa [prefixWord, tailWord_1734455, baseEnd_1734455] using wordTrace_append hprefix tailTrace_1734455
  have hstable : (prefixWord ++ tailWord_1734455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734455).length < 2 ^ (prefixWord ++ tailWord_1734455).sum := by decide
  have hdescent : baseEnd_1734455 < baseStart_1734455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734458 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_1734458 : Nat := 118140960795 + 1734458 * 2 ^ 59
def prefixEnd_1734458 : Nat := 4983230072969 + 3 ^ 40 * 1734458 * 2
def baseEnd_1734458 : Nat := 395826946238257848354835

theorem tailTrace_1734458 : CollatzResearch.WordTrace tailWord_1734458 prefixEnd_1734458 395826946238257848354835 := by
  unfold tailWord_1734458
  simp only [CollatzResearch.WordTrace]
  refine ⟨15815220087590590672021007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42173920233574908458722685 15815220087590590672021007)
  ·
    refine ⟨23722830131385886008031511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15815220087590590672021007 23722830131385886008031511)
    ·
      refine ⟨35584245197078829012047267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23722830131385886008031511 35584245197078829012047267)
      ·
        refine ⟨53376367795618243518070901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35584245197078829012047267 53376367795618243518070901)
        ·
          refine ⟨5004034480839210329819147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53376367795618243518070901 5004034480839210329819147)
          ·
            refine ⟨7506051721258815494728721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004034480839210329819147 7506051721258815494728721)
            ·
              refine ⟨5629538790944111621046541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7506051721258815494728721 5629538790944111621046541)
              ·
                refine ⟨2111077046604041857892453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5629538790944111621046541 2111077046604041857892453)
                ·
                  refine ⟨395826946238257848354835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2111077046604041857892453 395826946238257848354835)
                  ·
                    rfl

theorem cell21_1734458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_1734458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734458 prefixEnd_1734458 := by exact prefixLift 1734458
  have htrace : WordTrace (prefixWord ++ tailWord_1734458) baseStart_1734458 baseEnd_1734458 := by
    simpa [prefixWord, tailWord_1734458, baseEnd_1734458] using wordTrace_append hprefix tailTrace_1734458
  have hstable : (prefixWord ++ tailWord_1734458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734458).length < 2 ^ (prefixWord ++ tailWord_1734458).sum := by decide
  have hdescent : baseEnd_1734458 < baseStart_1734458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734492 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_1734492 : Nat := 118140960795 + 1734492 * 2 ^ 59
def prefixEnd_1734492 : Nat := 4983230072969 + 3 ^ 40 * 1734492 * 2
def baseEnd_1734492 : Nat := 395834705501481344788099

theorem tailTrace_1734492 : CollatzResearch.WordTrace tailWord_1734492 prefixEnd_1734492 395834705501481344788099 := by
  unfold tailWord_1734492
  simp only [CollatzResearch.WordTrace]
  refine ⟨31631060216119593247410865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42174746954826124329881153 31631060216119593247410865)
  ·
    refine ⟨23723295162089694935558149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31631060216119593247410865 23723295162089694935558149)
    ·
      refine ⟨4448117842891817800417153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23723295162089694935558149 4448117842891817800417153)
      ·
        refine ⟨3336088382168863350312865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4448117842891817800417153 3336088382168863350312865)
        ·
          refine ⟨2502066286626647512734649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3336088382168863350312865 2502066286626647512734649)
          ·
            refine ⟨1876549714969985634550987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2502066286626647512734649 1876549714969985634550987)
            ·
              refine ⟨2814824572454978451826481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876549714969985634550987 2814824572454978451826481)
              ·
                refine ⟨2111118429341233838869861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814824572454978451826481 2111118429341233838869861)
                ·
                  refine ⟨395834705501481344788099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2111118429341233838869861 395834705501481344788099)
                  ·
                    rfl

theorem cell21_1734492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_1734492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734492 prefixEnd_1734492 := by exact prefixLift 1734492
  have htrace : WordTrace (prefixWord ++ tailWord_1734492) baseStart_1734492 baseEnd_1734492 := by
    simpa [prefixWord, tailWord_1734492, baseEnd_1734492] using wordTrace_append hprefix tailTrace_1734492
  have hstable : (prefixWord ++ tailWord_1734492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734492).length < 2 ^ (prefixWord ++ tailWord_1734492).sum := by decide
  have hdescent : baseEnd_1734492 < baseStart_1734492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734503 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 5]
def baseStart_1734503 : Nat := 118140960795 + 1734503 * 2 ^ 59
def prefixEnd_1734503 : Nat := 4983230072969 + 3 ^ 40 * 1734503 * 2
def baseEnd_1734503 : Nat := 395837215851347770104743

theorem tailTrace_1734503 : CollatzResearch.WordTrace tailWord_1734503 prefixEnd_1734503 395837215851347770104743 := by
  unfold tailWord_1734503
  simp only [CollatzResearch.WordTrace]
  refine ⟨63262521635199335373472163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42175014423466223582314775 63262521635199335373472163)
  ·
    refine ⟨94893782452799003060208245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63262521635199335373472163 94893782452799003060208245)
    ·
      refine ⟨8896292104949906536894523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94893782452799003060208245 8896292104949906536894523)
      ·
        refine ⟨13344438157424859805341785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8896292104949906536894523 13344438157424859805341785)
        ·
          refine ⟨10008328618068644854006339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13344438157424859805341785 10008328618068644854006339)
          ·
            refine ⟨15012492927102967281009509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10008328618068644854006339 15012492927102967281009509)
            ·
              refine ⟨2814842423831806365189283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15012492927102967281009509 2814842423831806365189283)
              ·
                refine ⟨4222263635747709547783925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814842423831806365189283 4222263635747709547783925)
                ·
                  refine ⟨395837215851347770104743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4222263635747709547783925 395837215851347770104743)
                  ·
                    rfl

theorem cell21_1734503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 5].length) (baseStart_1734503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734503 prefixEnd_1734503 := by exact prefixLift 1734503
  have htrace : WordTrace (prefixWord ++ tailWord_1734503) baseStart_1734503 baseEnd_1734503 := by
    simpa [prefixWord, tailWord_1734503, baseEnd_1734503] using wordTrace_append hprefix tailTrace_1734503
  have hstable : (prefixWord ++ tailWord_1734503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734503).length < 2 ^ (prefixWord ++ tailWord_1734503).sum := by decide
  have hdescent : baseEnd_1734503 < baseStart_1734503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734548 : List Nat := [2, 4, 2, 1, 1, 2, 9]
def baseStart_1734548 : Nat := 118140960795 + 1734548 * 2 ^ 59
def prefixEnd_1734548 : Nat := 4983230072969 + 3 ^ 40 * 1734548 * 2
def baseEnd_1734548 : Nat := 43983053940493076872739

theorem tailTrace_1734548 : CollatzResearch.WordTrace tailWord_1734548 prefixEnd_1734548 43983053940493076872739 := by
  unfold tailWord_1734548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31632081460018154029430149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42176108613357538705906865 31632081460018154029430149)
  ·
    refine ⟨5931015273753403880518153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31632081460018154029430149 5931015273753403880518153)
    ·
      refine ⟨4448261455315052910388615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5931015273753403880518153 4448261455315052910388615)
      ·
        refine ⟨6672392182972579365582923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4448261455315052910388615 6672392182972579365582923)
        ·
          refine ⟨10008588274458869048374385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6672392182972579365582923 10008588274458869048374385)
          ·
            refine ⟨7506441205844151786280789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10008588274458869048374385 7506441205844151786280789)
            ·
              refine ⟨43983053940493076872739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7506441205844151786280789 43983053940493076872739)
              ·
                rfl

theorem cell21_1734548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 9].length) (baseStart_1734548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734548 prefixEnd_1734548 := by exact prefixLift 1734548
  have htrace : WordTrace (prefixWord ++ tailWord_1734548) baseStart_1734548 baseEnd_1734548 := by
    simpa [prefixWord, tailWord_1734548, baseEnd_1734548] using wordTrace_append hprefix tailTrace_1734548
  have hstable : (prefixWord ++ tailWord_1734548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734548).length < 2 ^ (prefixWord ++ tailWord_1734548).sum := by decide
  have hdescent : baseEnd_1734548 < baseStart_1734548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734568 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_1734568 : Nat := 118140960795 + 1734568 * 2 ^ 59
def prefixEnd_1734568 : Nat := 4983230072969 + 3 ^ 40 * 1734568 * 2
def baseEnd_1734568 : Nat := 395852049736922101521277

theorem tailTrace_1734568 : CollatzResearch.WordTrace tailWord_1734568 prefixEnd_1734568 395852049736922101521277 := by
  unfold tailWord_1734568
  simp only [CollatzResearch.WordTrace]
  refine ⟨31632446189981925737294179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42176594919975900983058905 31632446189981925737294179)
  ·
    refine ⟨47448669284972888605941269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31632446189981925737294179 47448669284972888605941269)
    ·
      refine ⟨2224156372733104153403497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47448669284972888605941269 2224156372733104153403497)
      ·
        refine ⟨1668117279549828115052623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2224156372733104153403497 1668117279549828115052623)
        ·
          refine ⟨2502175919324742172578935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668117279549828115052623 2502175919324742172578935)
          ·
            refine ⟨3753263878987113258868403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502175919324742172578935 3753263878987113258868403)
            ·
              refine ⟨5629895818480669888302605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753263878987113258868403 5629895818480669888302605)
              ·
                refine ⟨2111210931930251208113477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5629895818480669888302605 2111210931930251208113477)
                ·
                  refine ⟨395852049736922101521277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2111210931930251208113477 395852049736922101521277)
                  ·
                    rfl

theorem cell21_1734568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_1734568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734568 prefixEnd_1734568 := by exact prefixLift 1734568
  have htrace : WordTrace (prefixWord ++ tailWord_1734568) baseStart_1734568 baseEnd_1734568 := by
    simpa [prefixWord, tailWord_1734568, baseEnd_1734568] using wordTrace_append hprefix tailTrace_1734568
  have hstable : (prefixWord ++ tailWord_1734568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734568).length < 2 ^ (prefixWord ++ tailWord_1734568).sum := by decide
  have hdescent : baseEnd_1734568 < baseStart_1734568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734613 : List Nat := [1, 3, 2, 3, 2, 1, 4, 2, 3]
def baseStart_1734613 : Nat := 118140960795 + 1734613 * 2 ^ 59
def prefixEnd_1734613 : Nat := 4983230072969 + 3 ^ 40 * 1734613 * 2
def baseEnd_1734613 : Nat := 395862319350012023271185

theorem tailTrace_1734613 : CollatzResearch.WordTrace tailWord_1734613 prefixEnd_1734613 395862319350012023271185 := by
  unfold tailWord_1734613
  simp only [CollatzResearch.WordTrace]
  refine ⟨63266533664800824159976493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42177689109867216106650995 63266533664800824159976493)
  ·
    refine ⟨23724950124300309059991185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63266533664800824159976493 23724950124300309059991185)
    ·
      refine ⟨17793712593225231794993389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23724950124300309059991185 17793712593225231794993389)
      ·
        refine ⟨6672642222459461923122521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17793712593225231794993389 6672642222459461923122521)
        ·
          refine ⟨5004481666844596442341891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6672642222459461923122521 5004481666844596442341891)
          ·
            refine ⟨7506722500266894663512837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004481666844596442341891 7506722500266894663512837)
            ·
              refine ⟨1407510468800042749408657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7506722500266894663512837 1407510468800042749408657)
              ·
                refine ⟨1055632851600032062056493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407510468800042749408657 1055632851600032062056493)
                ·
                  refine ⟨395862319350012023271185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055632851600032062056493 395862319350012023271185)
                  ·
                    rfl

theorem cell21_1734613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_1734613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734613 prefixEnd_1734613 := by exact prefixLift 1734613
  have htrace : WordTrace (prefixWord ++ tailWord_1734613) baseStart_1734613 baseEnd_1734613 := by
    simpa [prefixWord, tailWord_1734613, baseEnd_1734613] using wordTrace_append hprefix tailTrace_1734613
  have hstable : (prefixWord ++ tailWord_1734613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734613).length < 2 ^ (prefixWord ++ tailWord_1734613).sum := by decide
  have hdescent : baseEnd_1734613 < baseStart_1734613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734641 : List Nat := [1, 2, 2, 2, 5, 1, 3, 5]
def baseStart_1734641 : Nat := 118140960795 + 1734641 * 2 ^ 59
def prefixEnd_1734641 : Nat := 4983230072969 + 3 ^ 40 * 1734641 * 2
def baseEnd_1734641 : Nat := 131956236443830065601487

theorem tailTrace_1734641 : CollatzResearch.WordTrace tailWord_1734641 prefixEnd_1734641 131956236443830065601487 := by
  unfold tailWord_1734641
  simp only [CollatzResearch.WordTrace]
  refine ⟨63267554908699384941995777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42178369939132923294663851 63267554908699384941995777)
  ·
    refine ⟨47450666181524538706496833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63267554908699384941995777 47450666181524538706496833)
    ·
      refine ⟨35587999636143404029872625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47450666181524538706496833 35587999636143404029872625)
      ·
        refine ⟨26690999727107553022404469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35587999636143404029872625 26690999727107553022404469)
        ·
          refine ⟨2502281224416333095850419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26690999727107553022404469 2502281224416333095850419)
          ·
            refine ⟨3753421836624499643775629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502281224416333095850419 3753421836624499643775629)
            ·
              refine ⟨1407533188734187366415861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3753421836624499643775629 1407533188734187366415861)
              ·
                refine ⟨131956236443830065601487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1407533188734187366415861 131956236443830065601487)
                ·
                  rfl

theorem cell21_1734641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 5].length) (baseStart_1734641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734641 prefixEnd_1734641 := by exact prefixLift 1734641
  have htrace : WordTrace (prefixWord ++ tailWord_1734641) baseStart_1734641 baseEnd_1734641 := by
    simpa [prefixWord, tailWord_1734641, baseEnd_1734641] using wordTrace_append hprefix tailTrace_1734641
  have hstable : (prefixWord ++ tailWord_1734641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734641).length < 2 ^ (prefixWord ++ tailWord_1734641).sum := by decide
  have hdescent : baseEnd_1734641 < baseStart_1734641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734745 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 4]
def baseStart_1734745 : Nat := 118140960795 + 1734745 * 2 ^ 59
def prefixEnd_1734745 : Nat := 4983230072969 + 3 ^ 40 * 1734745 * 2
def baseEnd_1734745 : Nat := 395892443548409127070915

theorem tailTrace_1734745 : CollatzResearch.WordTrace tailWord_1734745 prefixEnd_1734745 395892443548409127070915 := by
  unfold tailWord_1734745
  simp only [CollatzResearch.WordTrace]
  refine ⟨63271348100322610703781689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42180898733548407135854459 63271348100322610703781689)
  ·
    refine ⟨47453511075241958027836267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63271348100322610703781689 47453511075241958027836267)
    ·
      refine ⟨71180266612862937041754401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47453511075241958027836267 71180266612862937041754401)
      ·
        refine ⟨53385199959647202781315801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71180266612862937041754401 53385199959647202781315801)
        ·
          refine ⟨40038899969735402085986851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53385199959647202781315801 40038899969735402085986851)
          ·
            refine ⟨60058349954603103128980277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40038899969735402085986851 60058349954603103128980277)
            ·
              refine ⟨5630470308244040918341901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60058349954603103128980277 5630470308244040918341901)
              ·
                refine ⟨2111426365591515344378213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5630470308244040918341901 2111426365591515344378213)
                ·
                  refine ⟨395892443548409127070915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2111426365591515344378213 395892443548409127070915)
                  ·
                    rfl

theorem cell21_1734745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_1734745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734745 prefixEnd_1734745 := by exact prefixLift 1734745
  have htrace : WordTrace (prefixWord ++ tailWord_1734745) baseStart_1734745 baseEnd_1734745 := by
    simpa [prefixWord, tailWord_1734745, baseEnd_1734745] using wordTrace_append hprefix tailTrace_1734745
  have hstable : (prefixWord ++ tailWord_1734745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734745).length < 2 ^ (prefixWord ++ tailWord_1734745).sum := by decide
  have hdescent : baseEnd_1734745 < baseStart_1734745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734759 : List Nat := [1, 1, 5, 1, 1, 2, 1, 9]
def baseStart_1734759 : Nat := 118140960795 + 1734759 * 2 ^ 59
def prefixEnd_1734759 : Nat := 4983230072969 + 3 ^ 40 * 1734759 * 2
def baseEnd_1734759 : Nat := 131965212846382737945851

theorem tailTrace_1734759 : CollatzResearch.WordTrace tailWord_1734759 prefixEnd_1734759 131965212846382737945851 := by
  unfold tailWord_1734759
  simp only [CollatzResearch.WordTrace]
  refine ⟨63271858722271891094791331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42181239148181260729860887 63271858722271891094791331)
  ·
    refine ⟨94907788083407836642186997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63271858722271891094791331 94907788083407836642186997)
    ·
      refine ⟨8897605132819484685205031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94907788083407836642186997 8897605132819484685205031)
      ·
        refine ⟨13346407699229227027807547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8897605132819484685205031 13346407699229227027807547)
        ·
          refine ⟨20019611548843840541711321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13346407699229227027807547 20019611548843840541711321)
          ·
            refine ⟨15014708661632880406283491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20019611548843840541711321 15014708661632880406283491)
            ·
              refine ⟨22522062992449320609425237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15014708661632880406283491 22522062992449320609425237)
              ·
                refine ⟨131965212846382737945851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22522062992449320609425237 131965212846382737945851)
                ·
                  rfl

theorem cell21_1734759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 9].length) (baseStart_1734759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734759 prefixEnd_1734759 := by exact prefixLift 1734759
  have htrace : WordTrace (prefixWord ++ tailWord_1734759) baseStart_1734759 baseEnd_1734759 := by
    simpa [prefixWord, tailWord_1734759, baseEnd_1734759] using wordTrace_append hprefix tailTrace_1734759
  have hstable : (prefixWord ++ tailWord_1734759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734759).length < 2 ^ (prefixWord ++ tailWord_1734759).sum := by decide
  have hdescent : baseEnd_1734759 < baseStart_1734759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734807 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 5]
def baseStart_1734807 : Nat := 118140960795 + 1734807 * 2 ^ 59
def prefixEnd_1734807 : Nat := 4983230072969 + 3 ^ 40 * 1734807 * 2
def baseEnd_1734807 : Nat := 395906592793110797037455

theorem tailTrace_1734807 : CollatzResearch.WordTrace tailWord_1734807 prefixEnd_1734807 395906592793110797037455 := by
  unfold tailWord_1734807
  simp only [CollatzResearch.WordTrace]
  refine ⟨63273609426097995292538675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42182406284065330195025783 63273609426097995292538675)
  ·
    refine ⟨94910414139146992938808013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63273609426097995292538675 94910414139146992938808013)
    ·
      refine ⟨35591405302180122352053005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94910414139146992938808013 35591405302180122352053005)
      ·
        refine ⟨13346776988317545882019877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35591405302180122352053005 13346776988317545882019877)
        ·
          refine ⟨2502520685309539852878727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13346776988317545882019877 2502520685309539852878727)
          ·
            refine ⟨3753781027964309779318091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502520685309539852878727 3753781027964309779318091)
            ·
              refine ⟨5630671541946464668977137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753781027964309779318091 5630671541946464668977137)
              ·
                refine ⟨4223003656459848501732853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5630671541946464668977137 4223003656459848501732853)
                ·
                  refine ⟨395906592793110797037455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4223003656459848501732853 395906592793110797037455)
                  ·
                    rfl

theorem cell21_1734807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 5].length) (baseStart_1734807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734807 prefixEnd_1734807 := by exact prefixLift 1734807
  have htrace : WordTrace (prefixWord ++ tailWord_1734807) baseStart_1734807 baseEnd_1734807 := by
    simpa [prefixWord, tailWord_1734807, baseEnd_1734807] using wordTrace_append hprefix tailTrace_1734807
  have hstable : (prefixWord ++ tailWord_1734807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734807).length < 2 ^ (prefixWord ++ tailWord_1734807).sum := by decide
  have hdescent : baseEnd_1734807 < baseStart_1734807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734880 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_1734880 : Nat := 118140960795 + 1734880 * 2 ^ 59
def prefixEnd_1734880 : Nat := 4983230072969 + 3 ^ 40 * 1734880 * 2
def baseEnd_1734880 : Nat := 395923252387678892320639

theorem tailTrace_1734880 : CollatzResearch.WordTrace tailWord_1734880 prefixEnd_1734880 395923252387678892320639 := by
  unfold tailWord_1734880
  simp only [CollatzResearch.WordTrace]
  refine ⟨31638135977416764379973047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42184181303222352506630729 31638135977416764379973047)
  ·
    refine ⟨47457203966125146569959571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31638135977416764379973047 47457203966125146569959571)
    ·
      refine ⟨71185805949187719854939357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47457203966125146569959571 71185805949187719854939357)
      ·
        refine ⟨26694677230945394945602259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71185805949187719854939357 26694677230945394945602259)
        ·
          refine ⟨40042015846418092418403389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26694677230945394945602259 40042015846418092418403389)
          ·
            refine ⟨15015755942406784656901271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40042015846418092418403389 15015755942406784656901271)
            ·
              refine ⟨22523633913610176985351907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15015755942406784656901271 22523633913610176985351907)
              ·
                refine ⟨33785450870415265478027861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22523633913610176985351907 33785450870415265478027861)
                ·
                  refine ⟨395923252387678892320639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33785450870415265478027861 395923252387678892320639)
                  ·
                    rfl

theorem cell21_1734880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_1734880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734880 prefixEnd_1734880 := by exact prefixLift 1734880
  have htrace : WordTrace (prefixWord ++ tailWord_1734880) baseStart_1734880 baseEnd_1734880 := by
    simpa [prefixWord, tailWord_1734880, baseEnd_1734880] using wordTrace_append hprefix tailTrace_1734880
  have hstable : (prefixWord ++ tailWord_1734880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734880).length < 2 ^ (prefixWord ++ tailWord_1734880).sum := by decide
  have hdescent : baseEnd_1734880 < baseStart_1734880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734911 : List Nat := [1, 1, 2, 2, 1, 4, 4, 6]
def baseStart_1734911 : Nat := 118140960795 + 1734911 * 2 ^ 59
def prefixEnd_1734911 : Nat := 4983230072969 + 3 ^ 40 * 1734911 * 2
def baseEnd_1734911 : Nat := 131976775670009909101303

theorem tailTrace_1734911 : CollatzResearch.WordTrace tailWord_1734911 prefixEnd_1734911 131976775670009909101303 := by
  unfold tailWord_1734911
  simp only [CollatzResearch.WordTrace]
  refine ⟨63277402617721221054324587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42184935078480814036216391 63277402617721221054324587)
  ·
    refine ⟨94916103926581831581486881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63277402617721221054324587 94916103926581831581486881)
    ·
      refine ⟨71187077944936373686115161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94916103926581831581486881 71187077944936373686115161)
      ·
        refine ⟨53390308458702280264586371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71187077944936373686115161 53390308458702280264586371)
        ·
          refine ⟨80085462688053420396879557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53390308458702280264586371 80085462688053420396879557)
          ·
            refine ⟨15016024254010016324414917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80085462688053420396879557 15016024254010016324414917)
            ·
              refine ⟨2815504547626878060827797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15016024254010016324414917 2815504547626878060827797)
              ·
                refine ⟨131976775670009909101303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2815504547626878060827797 131976775670009909101303)
                ·
                  rfl

theorem cell21_1734911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 6].length) (baseStart_1734911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734911 prefixEnd_1734911 := by exact prefixLift 1734911
  have htrace : WordTrace (prefixWord ++ tailWord_1734911) baseStart_1734911 baseEnd_1734911 := by
    simpa [prefixWord, tailWord_1734911, baseEnd_1734911] using wordTrace_append hprefix tailTrace_1734911
  have hstable : (prefixWord ++ tailWord_1734911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734911).length < 2 ^ (prefixWord ++ tailWord_1734911).sum := by decide
  have hdescent : baseEnd_1734911 < baseStart_1734911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1734956 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_1734956 : Nat := 118140960795 + 1734956 * 2 ^ 59
def prefixEnd_1734956 : Nat := 4983230072969 + 3 ^ 40 * 1734956 * 2
def baseEnd_1734956 : Nat := 395940596623119649053817

theorem tailTrace_1734956 : CollatzResearch.WordTrace tailWord_1734956 prefixEnd_1734956 395940596623119649053817 := by
  unfold tailWord_1734956
  simp only [CollatzResearch.WordTrace]
  refine ⟨31639521951279096869856361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42186029268372129159808481 31639521951279096869856361)
  ·
    refine ⟨23729641463459322652392271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31639521951279096869856361 23729641463459322652392271)
    ·
      refine ⟨35594462195188983978588407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23729641463459322652392271 35594462195188983978588407)
      ·
        refine ⟨53391693292783475967882611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35594462195188983978588407 53391693292783475967882611)
        ·
          refine ⟨80087539939175213951823917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53391693292783475967882611 80087539939175213951823917)
          ·
            refine ⟨30032827477190705231933969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80087539939175213951823917 30032827477190705231933969)
            ·
              refine ⟨22524620607893028923950477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30032827477190705231933969 22524620607893028923950477)
              ·
                refine ⟨8446732727959885846481429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22524620607893028923950477 8446732727959885846481429)
                ·
                  refine ⟨395940596623119649053817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8446732727959885846481429 395940596623119649053817)
                  ·
                    rfl

theorem cell21_1734956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_1734956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1734956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1734956 prefixEnd_1734956 := by exact prefixLift 1734956
  have htrace : WordTrace (prefixWord ++ tailWord_1734956) baseStart_1734956 baseEnd_1734956 := by
    simpa [prefixWord, tailWord_1734956, baseEnd_1734956] using wordTrace_append hprefix tailTrace_1734956
  have hstable : (prefixWord ++ tailWord_1734956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1734956).length < 2 ^ (prefixWord ++ tailWord_1734956).sum := by decide
  have hdescent : baseEnd_1734956 < baseStart_1734956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1734956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735001 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 9]
def baseStart_1735001 : Nat := 118140960795 + 1735001 * 2 ^ 59
def prefixEnd_1735001 : Nat := 4983230072969 + 3 ^ 40 * 1735001 * 2
def baseEnd_1735001 : Nat := 395950866236209570803725

theorem tailTrace_1735001 : CollatzResearch.WordTrace tailWord_1735001 prefixEnd_1735001 395950866236209570803725 := by
  unfold tailWord_1735001
  simp only [CollatzResearch.WordTrace]
  refine ⟨63280685187395166425100857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42187123458263444283400571 63280685187395166425100857)
  ·
    refine ⟨47460513890546374818825643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63280685187395166425100857 47460513890546374818825643)
    ·
      refine ⟨71190770835819562228238465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47460513890546374818825643 71190770835819562228238465)
      ·
        refine ⟨53393078126864671671178849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71190770835819562228238465 53393078126864671671178849)
        ·
          refine ⟨40044808595148503753384137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53393078126864671671178849 40044808595148503753384137)
          ·
            refine ⟨30033606446361377815038103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40044808595148503753384137 30033606446361377815038103)
            ·
              refine ⟨45050409669542066722557155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30033606446361377815038103 45050409669542066722557155)
              ·
                refine ⟨67575614504313100083835733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45050409669542066722557155 67575614504313100083835733)
                ·
                  refine ⟨395950866236209570803725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67575614504313100083835733 395950866236209570803725)
                  ·
                    rfl

theorem cell21_1735001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_1735001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735001 prefixEnd_1735001 := by exact prefixLift 1735001
  have htrace : WordTrace (prefixWord ++ tailWord_1735001) baseStart_1735001 baseEnd_1735001 := by
    simpa [prefixWord, tailWord_1735001, baseEnd_1735001] using wordTrace_append hprefix tailTrace_1735001
  have hstable : (prefixWord ++ tailWord_1735001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735001).length < 2 ^ (prefixWord ++ tailWord_1735001).sum := by decide
  have hdescent : baseEnd_1735001 < baseStart_1735001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735052 : List Nat := [2, 2, 1, 2, 1, 6, 1, 3, 3]
def baseStart_1735052 : Nat := 118140960795 + 1735052 * 2 ^ 59
def prefixEnd_1735052 : Nat := 4983230072969 + 3 ^ 40 * 1735052 * 2
def baseEnd_1735052 : Nat := 395962505131044815453621

theorem tailTrace_1735052 : CollatzResearch.WordTrace tailWord_1735052 prefixEnd_1735052 395962505131044815453621 := by
  unfold tailWord_1735052
  simp only [CollatzResearch.WordTrace]
  refine ⟨31641272655105201067603705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42188363540140268090138273 31641272655105201067603705)
  ·
    refine ⟨23730954491328900800702779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31641272655105201067603705 23730954491328900800702779)
    ·
      refine ⟨35596431736993351201054169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23730954491328900800702779 35596431736993351201054169)
      ·
        refine ⟨26697323802745013400790627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35596431736993351201054169 26697323802745013400790627)
        ·
          refine ⟨40045985704117520101185941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26697323802745013400790627 40045985704117520101185941)
          ·
            refine ⟨1877155579880508754743091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40045985704117520101185941 1877155579880508754743091)
            ·
              refine ⟨2815733369820763132114637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877155579880508754743091 2815733369820763132114637)
              ·
                refine ⟨1055900013682786174542989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2815733369820763132114637 1055900013682786174542989)
                ·
                  refine ⟨395962505131044815453621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055900013682786174542989 395962505131044815453621)
                  ·
                    rfl

theorem cell21_1735052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_1735052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735052 prefixEnd_1735052 := by exact prefixLift 1735052
  have htrace : WordTrace (prefixWord ++ tailWord_1735052) baseStart_1735052 baseEnd_1735052 := by
    simpa [prefixWord, tailWord_1735052, baseEnd_1735052] using wordTrace_append hprefix tailTrace_1735052
  have hstable : (prefixWord ++ tailWord_1735052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735052).length < 2 ^ (prefixWord ++ tailWord_1735052).sum := by decide
  have hdescent : baseEnd_1735052 < baseStart_1735052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735069 : List Nat := [1, 4, 2, 1, 4, 1, 3, 2, 3]
def baseStart_1735069 : Nat := 118140960795 + 1735069 * 2 ^ 59
def prefixEnd_1735069 : Nat := 4983230072969 + 3 ^ 40 * 1735069 * 2
def baseEnd_1735069 : Nat := 395966384762656563670253

theorem tailTrace_1735069 : CollatzResearch.WordTrace tailWord_1735069 prefixEnd_1735069 395966384762656563670253 := by
  unfold tailWord_1735069
  simp only [CollatzResearch.WordTrace]
  refine ⟨63283165351148814038576261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42188776900765876025717507 63283165351148814038576261)
  ·
    refine ⟨11865593503340402632233049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63283165351148814038576261 11865593503340402632233049)
    ·
      refine ⟨8899195127505301974174787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11865593503340402632233049 8899195127505301974174787)
      ·
        refine ⟨13348792691257952961262181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8899195127505301974174787 13348792691257952961262181)
        ·
          refine ⟨2502898629610866180236659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13348792691257952961262181 2502898629610866180236659)
          ·
            refine ⟨3754347944416299270354989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502898629610866180236659 3754347944416299270354989)
            ·
              refine ⟨1407880479156112226383121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3754347944416299270354989 1407880479156112226383121)
              ·
                refine ⟨1055910359367084169787341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407880479156112226383121 1055910359367084169787341)
                ·
                  refine ⟨395966384762656563670253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055910359367084169787341 395966384762656563670253)
                  ·
                    rfl

theorem cell21_1735069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_1735069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735069 prefixEnd_1735069 := by exact prefixLift 1735069
  have htrace : WordTrace (prefixWord ++ tailWord_1735069) baseStart_1735069 baseEnd_1735069 := by
    simpa [prefixWord, tailWord_1735069, baseEnd_1735069] using wordTrace_append hprefix tailTrace_1735069
  have hstable : (prefixWord ++ tailWord_1735069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735069).length < 2 ^ (prefixWord ++ tailWord_1735069).sum := by decide
  have hdescent : baseEnd_1735069 < baseStart_1735069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735080 : List Nat := [2, 1, 6, 1, 1, 1, 1, 8]
def baseStart_1735080 : Nat := 118140960795 + 1735080 * 2 ^ 59
def prefixEnd_1735080 : Nat := 4983230072969 + 3 ^ 40 * 1735080 * 2
def baseEnd_1735080 : Nat := 131989631704174329662299

theorem tailTrace_1735080 : CollatzResearch.WordTrace tailWord_1735080 prefixEnd_1735080 131989631704174329662299 := by
  unfold tailWord_1735080
  simp only [CollatzResearch.WordTrace]
  refine ⟨31641783277054481458613347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42189044369405975278151129 31641783277054481458613347)
  ·
    refine ⟨47462674915581722187920021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31641783277054481458613347 47462674915581722187920021)
    ·
      refine ⟨2224812886667893227558751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47462674915581722187920021 2224812886667893227558751)
      ·
        refine ⟨3337219330001839841338127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224812886667893227558751 3337219330001839841338127)
        ·
          refine ⟨5005828995002759762007191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3337219330001839841338127 5005828995002759762007191)
          ·
            refine ⟨7508743492504139643010787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5005828995002759762007191 7508743492504139643010787)
            ·
              refine ⟨11263115238756209464516181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508743492504139643010787 11263115238756209464516181)
              ·
                refine ⟨131989631704174329662299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11263115238756209464516181 131989631704174329662299)
                ·
                  rfl

theorem cell21_1735080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_1735080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735080 prefixEnd_1735080 := by exact prefixLift 1735080
  have htrace : WordTrace (prefixWord ++ tailWord_1735080) baseStart_1735080 baseEnd_1735080 := by
    simpa [prefixWord, tailWord_1735080, baseEnd_1735080] using wordTrace_append hprefix tailTrace_1735080
  have hstable : (prefixWord ++ tailWord_1735080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735080).length < 2 ^ (prefixWord ++ tailWord_1735080).sum := by decide
  have hdescent : baseEnd_1735080 < baseStart_1735080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735125 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 4]
def baseStart_1735125 : Nat := 118140960795 + 1735125 * 2 ^ 59
def prefixEnd_1735125 : Nat := 4983230072969 + 3 ^ 40 * 1735125 * 2
def baseEnd_1735125 : Nat := 395979164725612910736805

theorem tailTrace_1735125 : CollatzResearch.WordTrace tailWord_1735125 prefixEnd_1735125 395979164725612910736805 := by
  unfold tailWord_1735125
  simp only [CollatzResearch.WordTrace]
  refine ⟨63285207838945935602614829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42190138559297290401743219 63285207838945935602614829)
  ·
    refine ⟨23731952939604725850980561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63285207838945935602614829 23731952939604725850980561)
    ·
      refine ⟨17798964704703544388235421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23731952939604725850980561 17798964704703544388235421)
      ·
        refine ⟨6674611764263829145588283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17798964704703544388235421 6674611764263829145588283)
        ·
          refine ⟨10011917646395743718382425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674611764263829145588283 10011917646395743718382425)
          ·
            refine ⟨7508938234796807788786819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10011917646395743718382425 7508938234796807788786819)
            ·
              refine ⟨11263407352195211683180229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508938234796807788786819 11263407352195211683180229)
              ·
                refine ⟨2111888878536602190596293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11263407352195211683180229 2111888878536602190596293)
                ·
                  refine ⟨395979164725612910736805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2111888878536602190596293 395979164725612910736805)
                  ·
                    rfl

theorem cell21_1735125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_1735125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735125 prefixEnd_1735125 := by exact prefixLift 1735125
  have htrace : WordTrace (prefixWord ++ tailWord_1735125) baseStart_1735125 baseEnd_1735125 := by
    simpa [prefixWord, tailWord_1735125, baseEnd_1735125] using wordTrace_append hprefix tailTrace_1735125
  have hstable : (prefixWord ++ tailWord_1735125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735125).length < 2 ^ (prefixWord ++ tailWord_1735125).sum := by decide
  have hdescent : baseEnd_1735125 < baseStart_1735125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735207 : List Nat := [1, 1, 7, 2, 2, 1, 2, 5]
def baseStart_1735207 : Nat := 118140960795 + 1735207 * 2 ^ 59
def prefixEnd_1735207 : Nat := 4983230072969 + 3 ^ 40 * 1735207 * 2
def baseEnd_1735207 : Nat := 131999292747599663456657

theorem tailTrace_1735207 : CollatzResearch.WordTrace tailWord_1735207 prefixEnd_1735207 131999292747599663456657 := by
  unfold tailWord_1735207
  simp only [CollatzResearch.WordTrace]
  refine ⟨63288198624648863607099875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42192132416432575738066583 63288198624648863607099875)
  ·
    refine ⟨94932297936973295410649813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63288198624648863607099875 94932297936973295410649813)
    ·
      refine ⟨2224975732897811611187105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 94932297936973295410649813 2224975732897811611187105)
      ·
        refine ⟨1668731799673358708390329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2224975732897811611187105 1668731799673358708390329)
        ·
          refine ⟨1251548849755019031292747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668731799673358708390329 1251548849755019031292747)
          ·
            refine ⟨1877323274632528546939121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251548849755019031292747 1877323274632528546939121)
            ·
              refine ⟨1407992455974396410204341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877323274632528546939121 1407992455974396410204341)
              ·
                refine ⟨131999292747599663456657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1407992455974396410204341 131999292747599663456657)
                ·
                  rfl

theorem cell21_1735207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 5].length) (baseStart_1735207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735207 prefixEnd_1735207 := by exact prefixLift 1735207
  have htrace : WordTrace (prefixWord ++ tailWord_1735207) baseStart_1735207 baseEnd_1735207 := by
    simpa [prefixWord, tailWord_1735207, baseEnd_1735207] using wordTrace_append hprefix tailTrace_1735207
  have hstable : (prefixWord ++ tailWord_1735207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735207).length < 2 ^ (prefixWord ++ tailWord_1735207).sum := by decide
  have hdescent : baseEnd_1735207 < baseStart_1735207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735238 : List Nat := [6, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1735238 : Nat := 118140960795 + 1735238 * 2 ^ 59
def prefixEnd_1735238 : Nat := 4983230072969 + 3 ^ 40 * 1735238 * 2
def baseEnd_1735238 : Nat := 396004952865149825353241

theorem tailTrace_1735238 : CollatzResearch.WordTrace tailWord_1735238 prefixEnd_1735238 396004952865149825353241 := by
  unfold tailWord_1735238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977791540235517371921199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42192886191691037267652245 1977791540235517371921199)
  ·
    refine ⟨2966687310353276057881799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1977791540235517371921199 2966687310353276057881799)
    ·
      refine ⟨4450030965529914086822699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966687310353276057881799 4450030965529914086822699)
      ·
        refine ⟨6675046448294871130234049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4450030965529914086822699 6675046448294871130234049)
        ·
          refine ⟨5006284836221153347675537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6675046448294871130234049 5006284836221153347675537)
          ·
            refine ⟨3754713627165865010756653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006284836221153347675537 3754713627165865010756653)
            ·
              refine ⟨1408017610187199379033745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3754713627165865010756653 1408017610187199379033745)
              ·
                refine ⟨1056013207640399534275309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408017610187199379033745 1056013207640399534275309)
                ·
                  refine ⟨396004952865149825353241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056013207640399534275309 396004952865149825353241)
                  ·
                    rfl

theorem cell21_1735238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1735238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735238 prefixEnd_1735238 := by exact prefixLift 1735238
  have htrace : WordTrace (prefixWord ++ tailWord_1735238) baseStart_1735238 baseEnd_1735238 := by
    simpa [prefixWord, tailWord_1735238, baseEnd_1735238] using wordTrace_append hprefix tailTrace_1735238
  have hstable : (prefixWord ++ tailWord_1735238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735238).length < 2 ^ (prefixWord ++ tailWord_1735238).sum := by decide
  have hdescent : baseEnd_1735238 < baseStart_1735238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735246 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_1735246 : Nat := 118140960795 + 1735246 * 2 ^ 59
def prefixEnd_1735246 : Nat := 4983230072969 + 3 ^ 40 * 1735246 * 2
def baseEnd_1735246 : Nat := 396006778574143589219891

theorem tailTrace_1735246 : CollatzResearch.WordTrace tailWord_1735246 prefixEnd_1735246 396006778574143589219891 := by
  unfold tailWord_1735246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7911202633938446658471199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42193080714338382178513061 7911202633938446658471199)
  ·
    refine ⟨11866803950907669987706799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7911202633938446658471199 11866803950907669987706799)
    ·
      refine ⟨17800205926361504981560199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11866803950907669987706799 17800205926361504981560199)
      ·
        refine ⟨26700308889542257472340299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17800205926361504981560199 26700308889542257472340299)
        ·
          refine ⟨40050463334313386208510449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26700308889542257472340299 40050463334313386208510449)
          ·
            refine ⟨30037847500735039656382837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40050463334313386208510449 30037847500735039656382837)
            ·
              refine ⟨2816048203193909967785891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30037847500735039656382837 2816048203193909967785891)
              ·
                refine ⟨4224072304790864951678837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816048203193909967785891 4224072304790864951678837)
                ·
                  refine ⟨396006778574143589219891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4224072304790864951678837 396006778574143589219891)
                  ·
                    rfl

theorem cell21_1735246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_1735246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735246 prefixEnd_1735246 := by exact prefixLift 1735246
  have htrace : WordTrace (prefixWord ++ tailWord_1735246) baseStart_1735246 baseEnd_1735246 := by
    simpa [prefixWord, tailWord_1735246, baseEnd_1735246] using wordTrace_append hprefix tailTrace_1735246
  have hstable : (prefixWord ++ tailWord_1735246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735246).length < 2 ^ (prefixWord ++ tailWord_1735246).sum := by decide
  have hdescent : baseEnd_1735246 < baseStart_1735246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735305 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 5]
def baseStart_1735305 : Nat := 118140960795 + 1735305 * 2 ^ 59
def prefixEnd_1735305 : Nat := 4983230072969 + 3 ^ 40 * 1735305 * 2
def baseEnd_1735305 : Nat := 396020243177972597736437

theorem tailTrace_1735305 : CollatzResearch.WordTrace tailWord_1735305 prefixEnd_1735305 396020243177972597736437 := by
  unfold tailWord_1735305
  simp only [CollatzResearch.WordTrace]
  refine ⟨63291772978293826344167369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42194515318862550896111579 63291772978293826344167369)
  ·
    refine ⟨47468829733720369758125527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63291772978293826344167369 47468829733720369758125527)
    ·
      refine ⟨71203244600580554637188291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47468829733720369758125527 71203244600580554637188291)
      ·
        refine ⟨106804866900870831955782437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71203244600580554637188291 106804866900870831955782437)
        ·
          refine ⟨20025912543913280991709207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106804866900870831955782437 20025912543913280991709207)
          ·
            refine ⟨30038868815869921487563811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20025912543913280991709207 30038868815869921487563811)
            ·
              refine ⟨45058303223804882231345717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30038868815869921487563811 45058303223804882231345717)
              ·
                refine ⟨4224215927231707709188661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45058303223804882231345717 4224215927231707709188661)
                ·
                  refine ⟨396020243177972597736437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4224215927231707709188661 396020243177972597736437)
                  ·
                    rfl

theorem cell21_1735305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_1735305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735305 prefixEnd_1735305 := by exact prefixLift 1735305
  have htrace : WordTrace (prefixWord ++ tailWord_1735305) baseStart_1735305 baseEnd_1735305 := by
    simpa [prefixWord, tailWord_1735305, baseEnd_1735305] using wordTrace_append hprefix tailTrace_1735305
  have hstable : (prefixWord ++ tailWord_1735305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735305).length < 2 ^ (prefixWord ++ tailWord_1735305).sum := by decide
  have hdescent : baseEnd_1735305 < baseStart_1735305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735370 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_1735370 : Nat := 118140960795 + 1735370 * 2 ^ 59
def prefixEnd_1735370 : Nat := 4983230072969 + 3 ^ 40 * 1735370 * 2
def baseEnd_1735370 : Nat := 396035077063546929152971

theorem tailTrace_1735370 : CollatzResearch.WordTrace tailWord_1735370 prefixEnd_1735370 396035077063546929152971 := by
  unfold tailWord_1735370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15823535930764585611320891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42196095815372228296855709 15823535930764585611320891)
  ·
    refine ⟨23735303896146878416981337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15823535930764585611320891 23735303896146878416981337)
    ·
      refine ⟨17801477922110158812736003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23735303896146878416981337 17801477922110158812736003)
      ·
        refine ⟨26702216883165238219104005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17801477922110158812736003 26702216883165238219104005)
        ·
          refine ⟨5006665665593482166082001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26702216883165238219104005 5006665665593482166082001)
          ·
            refine ⟨3754999249195111624561501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5006665665593482166082001 3754999249195111624561501)
            ·
              refine ⟨1408124718448166859210563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3754999249195111624561501 1408124718448166859210563)
              ·
                refine ⟨2112187077672250288815845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408124718448166859210563 2112187077672250288815845)
                ·
                  refine ⟨396035077063546929152971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2112187077672250288815845 396035077063546929152971)
                  ·
                    rfl

theorem cell21_1735370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_1735370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735370 prefixEnd_1735370 := by exact prefixLift 1735370
  have htrace : WordTrace (prefixWord ++ tailWord_1735370) baseStart_1735370 baseEnd_1735370 := by
    simpa [prefixWord, tailWord_1735370, baseEnd_1735370] using wordTrace_append hprefix tailTrace_1735370
  have hstable : (prefixWord ++ tailWord_1735370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735370).length < 2 ^ (prefixWord ++ tailWord_1735370).sum := by decide
  have hdescent : baseEnd_1735370 < baseStart_1735370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735384 : List Nat := [2, 1, 2, 2, 3, 4, 2, 5]
def baseStart_1735384 : Nat := 118140960795 + 1735384 * 2 ^ 59
def prefixEnd_1735384 : Nat := 4983230072969 + 3 ^ 40 * 1735384 * 2
def baseEnd_1735384 : Nat := 132012757351428671973203

theorem tailTrace_1735384 : CollatzResearch.WordTrace tailWord_1735384 prefixEnd_1735384 132012757351428671973203 := by
  unfold tailWord_1735384
  simp only [CollatzResearch.WordTrace]
  refine ⟨31647327172503811418146603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42196436230005081890862137 31647327172503811418146603)
  ·
    refine ⟨47470990758755717127219905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31647327172503811418146603 47470990758755717127219905)
    ·
      refine ⟨35603243069066787845414929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47470990758755717127219905 35603243069066787845414929)
      ·
        refine ⟨26702432301800090884061197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35603243069066787845414929 26702432301800090884061197)
        ·
          refine ⟨10013412113175034081522949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26702432301800090884061197 10013412113175034081522949)
          ·
            refine ⟨1877514771220318890285553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10013412113175034081522949 1877514771220318890285553)
            ·
              refine ⟨1408136078415239167714165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877514771220318890285553 1408136078415239167714165)
              ·
                refine ⟨132012757351428671973203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1408136078415239167714165 132012757351428671973203)
                ·
                  rfl

theorem cell21_1735384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_1735384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735384 prefixEnd_1735384 := by exact prefixLift 1735384
  have htrace : WordTrace (prefixWord ++ tailWord_1735384) baseStart_1735384 baseEnd_1735384 := by
    simpa [prefixWord, tailWord_1735384, baseEnd_1735384] using wordTrace_append hprefix tailTrace_1735384
  have hstable : (prefixWord ++ tailWord_1735384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735384).length < 2 ^ (prefixWord ++ tailWord_1735384).sum := by decide
  have hdescent : baseEnd_1735384 < baseStart_1735384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735466 : List Nat := [3, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_1735466 : Nat := 118140960795 + 1735466 * 2 ^ 59
def prefixEnd_1735466 : Nat := 4983230072969 + 3 ^ 40 * 1735466 * 2
def baseEnd_1735466 : Nat := 396056985571472095552775

theorem tailTrace_1735466 : CollatzResearch.WordTrace tailWord_1735466 prefixEnd_1735466 396056985571472095552775 := by
  unfold tailWord_1735466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15824411282677637710194563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42198430087140367227185501 15824411282677637710194563)
  ·
    refine ⟨23736616924016456565291845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15824411282677637710194563 23736616924016456565291845)
    ·
      refine ⟨4450615673253085605992221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23736616924016456565291845 4450615673253085605992221)
      ·
        refine ⟨1668980877469907102247083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4450615673253085605992221 1668980877469907102247083)
        ·
          refine ⟨2503471316204860653370625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668980877469907102247083 2503471316204860653370625)
          ·
            refine ⟨1877603487153645490027969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2503471316204860653370625 1877603487153645490027969)
            ·
              refine ⟨1408202615365234117520977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877603487153645490027969 1408202615365234117520977)
              ·
                refine ⟨1056151961523925588140733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408202615365234117520977 1056151961523925588140733)
                ·
                  refine ⟨396056985571472095552775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056151961523925588140733 396056985571472095552775)
                  ·
                    rfl

theorem cell21_1735466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_1735466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735466 prefixEnd_1735466 := by exact prefixLift 1735466
  have htrace : WordTrace (prefixWord ++ tailWord_1735466) baseStart_1735466 baseEnd_1735466 := by
    simpa [prefixWord, tailWord_1735466, baseEnd_1735466] using wordTrace_append hprefix tailTrace_1735466
  have hstable : (prefixWord ++ tailWord_1735466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735466).length < 2 ^ (prefixWord ++ tailWord_1735466).sum := by decide
  have hdescent : baseEnd_1735466 < baseStart_1735466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735494 : List Nat := [6, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1735494 : Nat := 118140960795 + 1735494 * 2 ^ 59
def prefixEnd_1735494 : Nat := 4983230072969 + 3 ^ 40 * 1735494 * 2
def baseEnd_1735494 : Nat := 132021125184316756362017

theorem tailTrace_1735494 : CollatzResearch.WordTrace tailWord_1735494 prefixEnd_1735494 132021125184316756362017 := by
  unfold tailWord_1735494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978083324206534738212423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42199110916406074415198357 1978083324206534738212423)
  ·
    refine ⟨2967124986309802107318635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978083324206534738212423 2967124986309802107318635)
    ·
      refine ⟨4450687479464703160977953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967124986309802107318635 4450687479464703160977953)
      ·
        refine ⟨3338015609598527370733465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4450687479464703160977953 3338015609598527370733465)
        ·
          refine ⟨2503511707198895528050099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3338015609598527370733465 2503511707198895528050099)
          ·
            refine ⟨3755267560798343292075149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503511707198895528050099 3755267560798343292075149)
            ·
              refine ⟨1408225335299378734528181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3755267560798343292075149 1408225335299378734528181)
              ·
                refine ⟨132021125184316756362017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1408225335299378734528181 132021125184316756362017)
                ·
                  rfl

theorem cell21_1735494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1735494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735494 prefixEnd_1735494 := by exact prefixLift 1735494
  have htrace : WordTrace (prefixWord ++ tailWord_1735494) baseStart_1735494 baseEnd_1735494 := by
    simpa [prefixWord, tailWord_1735494, baseEnd_1735494] using wordTrace_append hprefix tailTrace_1735494
  have hstable : (prefixWord ++ tailWord_1735494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735494).length < 2 ^ (prefixWord ++ tailWord_1735494).sum := by decide
  have hdescent : baseEnd_1735494 < baseStart_1735494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735502 : List Nat := [4, 1, 1, 1, 1, 1, 1, 11]
def baseStart_1735502 : Nat := 118140960795 + 1735502 * 2 ^ 59
def prefixEnd_1735502 : Nat := 4983230072969 + 3 ^ 40 * 1735502 * 2
def baseEnd_1735502 : Nat := 132021733753981344317567

theorem tailTrace_1735502 : CollatzResearch.WordTrace tailWord_1735502 prefixEnd_1735502 132021733753981344317567 := by
  unfold tailWord_1735502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912369769822516123636095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42199305439053419326059173 7912369769822516123636095)
  ·
    refine ⟨11868554654733774185454143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7912369769822516123636095 11868554654733774185454143)
    ·
      refine ⟨17802831982100661278181215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11868554654733774185454143 17802831982100661278181215)
      ·
        refine ⟨26704247973150991917271823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17802831982100661278181215 26704247973150991917271823)
        ·
          refine ⟨40056371959726487875907735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26704247973150991917271823 40056371959726487875907735)
          ·
            refine ⟨60084557939589731813861603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40056371959726487875907735 60084557939589731813861603)
            ·
              refine ⟨90126836909384597720792405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60084557939589731813861603 90126836909384597720792405)
              ·
                refine ⟨132021733753981344317567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 90126836909384597720792405 132021733753981344317567)
                ·
                  rfl

theorem cell21_1735502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_1735502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735502 prefixEnd_1735502 := by exact prefixLift 1735502
  have htrace : WordTrace (prefixWord ++ tailWord_1735502) baseStart_1735502 baseEnd_1735502 := by
    simpa [prefixWord, tailWord_1735502, baseEnd_1735502] using wordTrace_append hprefix tailTrace_1735502
  have hstable : (prefixWord ++ tailWord_1735502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735502).length < 2 ^ (prefixWord ++ tailWord_1735502).sum := by decide
  have hdescent : baseEnd_1735502 < baseStart_1735502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735508 : List Nat := [2, 4, 1, 1, 4, 1, 2, 3, 3]
def baseStart_1735508 : Nat := 118140960795 + 1735508 * 2 ^ 59
def prefixEnd_1735508 : Nat := 4983230072969 + 3 ^ 40 * 1735508 * 2
def baseEnd_1735508 : Nat := 396066570543689355852689

theorem tailTrace_1735508 : CollatzResearch.WordTrace tailWord_1735508 prefixEnd_1735508 396066570543689355852689 := by
  unfold tailWord_1735508
  simp only [CollatzResearch.WordTrace]
  refine ⟨31649588498279196006903589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42199451331038928009204785 31649588498279196006903589)
  ·
    refine ⟨5934297843427349251294423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31649588498279196006903589 5934297843427349251294423)
    ·
      refine ⟨8901446765141023876941635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5934297843427349251294423 8901446765141023876941635)
      ·
        refine ⟨13352170147711535815412453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8901446765141023876941635 13352170147711535815412453)
        ·
          refine ⟨2503531902695912965389835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13352170147711535815412453 2503531902695912965389835)
          ·
            refine ⟨3755297854043869448084753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503531902695912965389835 3755297854043869448084753)
            ·
              refine ⟨2816473390532902086063565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755297854043869448084753 2816473390532902086063565)
              ·
                refine ⟨1056177521449838282273837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2816473390532902086063565 1056177521449838282273837)
                ·
                  refine ⟨396066570543689355852689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056177521449838282273837 396066570543689355852689)
                  ·
                    rfl

theorem cell21_1735508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_1735508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735508 prefixEnd_1735508 := by exact prefixLift 1735508
  have htrace : WordTrace (prefixWord ++ tailWord_1735508) baseStart_1735508 baseEnd_1735508 := by
    simpa [prefixWord, tailWord_1735508, baseEnd_1735508] using wordTrace_append hprefix tailTrace_1735508
  have hstable : (prefixWord ++ tailWord_1735508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735508).length < 2 ^ (prefixWord ++ tailWord_1735508).sum := by decide
  have hdescent : baseEnd_1735508 < baseStart_1735508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735623 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 8]
def baseStart_1735623 : Nat := 118140960795 + 1735623 * 2 ^ 59
def prefixEnd_1735623 : Nat := 4983230072969 + 3 ^ 40 * 1735623 * 2
def baseEnd_1735623 : Nat := 396092815110474711435787

theorem tailTrace_1735623 : CollatzResearch.WordTrace tailWord_1735623 prefixEnd_1735623 396092815110474711435787 := by
  unfold tailWord_1735623
  simp only [CollatzResearch.WordTrace]
  refine ⟨63303371391141766654243523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42202247594094511102829015 63303371391141766654243523)
  ·
    refine ⟨94955057086712649981365285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63303371391141766654243523 94955057086712649981365285)
    ·
      refine ⟨17804073203758621871505991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94955057086712649981365285 17804073203758621871505991)
      ·
        refine ⟨26706109805637932807258987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17804073203758621871505991 26706109805637932807258987)
        ·
          refine ⟨40059164708456899210888481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26706109805637932807258987 40059164708456899210888481)
          ·
            refine ⟨30044373531342674408166361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40059164708456899210888481 30044373531342674408166361)
            ·
              refine ⟨22533280148507005806124771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30044373531342674408166361 22533280148507005806124771)
              ·
                refine ⟨33799920222760508709187157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22533280148507005806124771 33799920222760508709187157)
                ·
                  refine ⟨396092815110474711435787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33799920222760508709187157 396092815110474711435787)
                  ·
                    rfl

theorem cell21_1735623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_1735623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735623 prefixEnd_1735623 := by exact prefixLift 1735623
  have htrace : WordTrace (prefixWord ++ tailWord_1735623) baseStart_1735623 baseEnd_1735623 := by
    simpa [prefixWord, tailWord_1735623, baseEnd_1735623] using wordTrace_append hprefix tailTrace_1735623
  have hstable : (prefixWord ++ tailWord_1735623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735623).length < 2 ^ (prefixWord ++ tailWord_1735623).sum := by decide
  have hdescent : baseEnd_1735623 < baseStart_1735623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735626 : List Nat := [3, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_1735626 : Nat := 118140960795 + 1735626 * 2 ^ 59
def prefixEnd_1735626 : Nat := 4983230072969 + 3 ^ 40 * 1735626 * 2
def baseEnd_1735626 : Nat := 396093499751347372885781

theorem tailTrace_1735626 : CollatzResearch.WordTrace tailWord_1735626 prefixEnd_1735626 396093499751347372885781 := by
  unfold tailWord_1735626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15825870202532724541650683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42202320540087265444401821 15825870202532724541650683)
  ·
    refine ⟨23738805303799086812476025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15825870202532724541650683 23738805303799086812476025)
    ·
      refine ⟨17804103977849315109357019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23738805303799086812476025 17804103977849315109357019)
      ·
        refine ⟨26706155966773972664035529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17804103977849315109357019 26706155966773972664035529)
        ·
          refine ⟨20029616975080479498026647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26706155966773972664035529 20029616975080479498026647)
          ·
            refine ⟨30044425462620719247039971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20029616975080479498026647 30044425462620719247039971)
            ·
              refine ⟨45066638193931078870559957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30044425462620719247039971 45066638193931078870559957)
              ·
                refine ⟨1056249332670259661028749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45066638193931078870559957 1056249332670259661028749)
                ·
                  refine ⟨396093499751347372885781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056249332670259661028749 396093499751347372885781)
                  ·
                    rfl

theorem cell21_1735626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_1735626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735626 prefixEnd_1735626 := by exact prefixLift 1735626
  have htrace : WordTrace (prefixWord ++ tailWord_1735626) baseStart_1735626 baseEnd_1735626 := by
    simpa [prefixWord, tailWord_1735626, baseEnd_1735626] using wordTrace_append hprefix tailTrace_1735626
  have hstable : (prefixWord ++ tailWord_1735626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735626).length < 2 ^ (prefixWord ++ tailWord_1735626).sum := by decide
  have hdescent : baseEnd_1735626 < baseStart_1735626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735629 : List Nat := [1, 6, 3, 1, 1, 9]
def baseStart_1735629 : Nat := 118140960795 + 1735629 * 2 ^ 59
def prefixEnd_1735629 : Nat := 4983230072969 + 3 ^ 40 * 1735629 * 2
def baseEnd_1735629 : Nat := 14670154977489630901325

theorem tailTrace_1735629 : CollatzResearch.WordTrace tailWord_1735629 prefixEnd_1735629 14670154977489630901325 := by
  unfold tailWord_1735629
  simp only [CollatzResearch.WordTrace]
  refine ⟨63303590229120029678961941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42202393486080019785974627 63303590229120029678961941)
  ·
    refine ⟨2967355791990001391201341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63303590229120029678961941 2967355791990001391201341)
    ·
      refine ⟨1112758421996250521700503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2967355791990001391201341 1112758421996250521700503)
      ·
        refine ⟨1669137632994375782550755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112758421996250521700503 1669137632994375782550755)
        ·
          refine ⟨2503706449491563673826133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669137632994375782550755 2503706449491563673826133)
          ·
            refine ⟨14670154977489630901325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2503706449491563673826133 14670154977489630901325)
            ·
              rfl

theorem cell21_1735629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 9].length) (baseStart_1735629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735629 prefixEnd_1735629 := by exact prefixLift 1735629
  have htrace : WordTrace (prefixWord ++ tailWord_1735629) baseStart_1735629 baseEnd_1735629 := by
    simpa [prefixWord, tailWord_1735629, baseEnd_1735629] using wordTrace_append hprefix tailTrace_1735629
  have hstable : (prefixWord ++ tailWord_1735629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735629).length < 2 ^ (prefixWord ++ tailWord_1735629).sum := by decide
  have hdescent : baseEnd_1735629 < baseStart_1735629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735640 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_1735640 : Nat := 118140960795 + 1735640 * 2 ^ 59
def prefixEnd_1735640 : Nat := 4983230072969 + 3 ^ 40 * 1735640 * 2
def baseEnd_1735640 : Nat := 396096694742086459652419

theorem tailTrace_1735640 : CollatzResearch.WordTrace tailWord_1735640 prefixEnd_1735640 396096694742086459652419 := by
  unfold tailWord_1735640
  simp only [CollatzResearch.WordTrace]
  refine ⟨31651995716040089278806187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42202660954720119038408249 31651995716040089278806187)
  ·
    refine ⟨47477993574060133918209281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31651995716040089278806187 47477993574060133918209281)
    ·
      refine ⟨35608495180545100438656961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47477993574060133918209281 35608495180545100438656961)
      ·
        refine ⟨26706371385408825328992721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35608495180545100438656961 26706371385408825328992721)
        ·
          refine ⟨20029778539056618996744541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26706371385408825328992721 20029778539056618996744541)
          ·
            refine ⟨7511166952146232123779203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20029778539056618996744541 7511166952146232123779203)
            ·
              refine ⟨11266750428219348185668805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511166952146232123779203 11266750428219348185668805)
              ·
                refine ⟨2112515705291127784812901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11266750428219348185668805 2112515705291127784812901)
                ·
                  refine ⟨396096694742086459652419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2112515705291127784812901 396096694742086459652419)
                  ·
                    rfl

theorem cell21_1735640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_1735640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735640 prefixEnd_1735640 := by exact prefixLift 1735640
  have htrace : WordTrace (prefixWord ++ tailWord_1735640) baseStart_1735640 baseEnd_1735640 := by
    simpa [prefixWord, tailWord_1735640, baseEnd_1735640] using wordTrace_append hprefix tailTrace_1735640
  have hstable : (prefixWord ++ tailWord_1735640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735640).length < 2 ^ (prefixWord ++ tailWord_1735640).sum := by decide
  have hdescent : baseEnd_1735640 < baseStart_1735640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735730 : List Nat := [3, 2, 1, 1, 2, 2, 3, 7]
def baseStart_1735730 : Nat := 118140960795 + 1735730 * 2 ^ 59
def prefixEnd_1735730 : Nat := 4983230072969 + 3 ^ 40 * 1735730 * 2
def baseEnd_1735730 : Nat := 132039077989422101050745

theorem tailTrace_1735730 : CollatzResearch.WordTrace tailWord_1735730 prefixEnd_1735730 132039077989422101050745 := by
  unfold tailWord_1735730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15826818500438530982097161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42204849334502749285592429 15826818500438530982097161)
  ·
    refine ⟨11870113875328898236572871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15826818500438530982097161 11870113875328898236572871)
    ·
      refine ⟨17805170812993347354859307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11870113875328898236572871 17805170812993347354859307)
      ·
        refine ⟨26707756219490021032288961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17805170812993347354859307 26707756219490021032288961)
        ·
          refine ⟨20030817164617515774216721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26707756219490021032288961 20030817164617515774216721)
          ·
            refine ⟨15023112873463136830662541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20030817164617515774216721 15023112873463136830662541)
            ·
              refine ⟨5633667327548676311498453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15023112873463136830662541 5633667327548676311498453)
              ·
                refine ⟨132039077989422101050745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5633667327548676311498453 132039077989422101050745)
                ·
                  rfl

theorem cell21_1735730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_1735730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735730 prefixEnd_1735730 := by exact prefixLift 1735730
  have htrace : WordTrace (prefixWord ++ tailWord_1735730) baseStart_1735730 baseEnd_1735730 := by
    simpa [prefixWord, tailWord_1735730, baseEnd_1735730] using wordTrace_append hprefix tailTrace_1735730
  have hstable : (prefixWord ++ tailWord_1735730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735730).length < 2 ^ (prefixWord ++ tailWord_1735730).sum := by decide
  have hdescent : baseEnd_1735730 < baseStart_1735730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735761 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 5]
def baseStart_1735761 : Nat := 118140960795 + 1735761 * 2 ^ 59
def prefixEnd_1735761 : Nat := 4983230072969 + 3 ^ 40 * 1735761 * 2
def baseEnd_1735761 : Nat := 396124308590617138135505

theorem tailTrace_1735761 : CollatzResearch.WordTrace tailWord_1735761 prefixEnd_1735761 396124308590617138135505 := by
  unfold tailWord_1735761
  simp only [CollatzResearch.WordTrace]
  refine ⟨63308404664641816222767137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42205603109761210815178091 63308404664641816222767137)
  ·
    refine ⟨47481303498481362167075353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63308404664641816222767137 47481303498481362167075353)
    ·
      refine ⟨35610977623861021625306515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47481303498481362167075353 35610977623861021625306515)
      ·
        refine ⟨53416466435791532437959773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35610977623861021625306515 53416466435791532437959773)
        ·
          refine ⟨20031174913421824664234915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53416466435791532437959773 20031174913421824664234915)
          ·
            refine ⟨30046762370132736996352373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20031174913421824664234915 30046762370132736996352373)
            ·
              refine ⟨2816883972199944093408035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30046762370132736996352373 2816883972199944093408035)
              ·
                refine ⟨4225325958299916140112053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816883972199944093408035 4225325958299916140112053)
                ·
                  refine ⟨396124308590617138135505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4225325958299916140112053 396124308590617138135505)
                  ·
                    rfl

theorem cell21_1735761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_1735761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735761 prefixEnd_1735761 := by exact prefixLift 1735761
  have htrace : WordTrace (prefixWord ++ tailWord_1735761) baseStart_1735761 baseEnd_1735761 := by
    simpa [prefixWord, tailWord_1735761, baseEnd_1735761] using wordTrace_append hprefix tailTrace_1735761
  have hstable : (prefixWord ++ tailWord_1735761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735761).length < 2 ^ (prefixWord ++ tailWord_1735761).sum := by decide
  have hdescent : baseEnd_1735761 < baseStart_1735761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735809 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 4]
def baseStart_1735809 : Nat := 118140960795 + 1735809 * 2 ^ 59
def prefixEnd_1735809 : Nat := 4983230072969 + 3 ^ 40 * 1735809 * 2
def baseEnd_1735809 : Nat := 396135262844579721335407

theorem tailTrace_1735809 : CollatzResearch.WordTrace tailWord_1735809 prefixEnd_1735809 396135262844579721335407 := by
  unfold tailWord_1735809
  simp only [CollatzResearch.WordTrace]
  refine ⟨63310155368467920420514481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42206770245645280280342987 63310155368467920420514481)
  ·
    refine ⟨47482616526350940315385861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63310155368467920420514481 47482616526350940315385861)
    ·
      refine ⟨8902990598690801309134849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47482616526350940315385861 8902990598690801309134849)
      ·
        refine ⟨6677242949018100981851137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8902990598690801309134849 6677242949018100981851137)
        ·
          refine ⟨5007932211763575736388353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6677242949018100981851137 5007932211763575736388353)
          ·
            refine ⟨3755949158822681802291265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5007932211763575736388353 3755949158822681802291265)
            ·
              refine ⟨2816961869117011351718449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755949158822681802291265 2816961869117011351718449)
              ·
                refine ⟨2112721401837758513788837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2816961869117011351718449 2112721401837758513788837)
                ·
                  refine ⟨396135262844579721335407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2112721401837758513788837 396135262844579721335407)
                  ·
                    rfl

theorem cell21_1735809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_1735809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735809 prefixEnd_1735809 := by exact prefixLift 1735809
  have htrace : WordTrace (prefixWord ++ tailWord_1735809) baseStart_1735809 baseEnd_1735809 := by
    simpa [prefixWord, tailWord_1735809, baseEnd_1735809] using wordTrace_append hprefix tailTrace_1735809
  have hstable : (prefixWord ++ tailWord_1735809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735809).length < 2 ^ (prefixWord ++ tailWord_1735809).sum := by decide
  have hdescent : baseEnd_1735809 < baseStart_1735809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735812 : List Nat := [2, 3, 2, 1, 2, 4, 2, 2, 3]
def baseStart_1735812 : Nat := 118140960795 + 1735812 * 2 ^ 59
def prefixEnd_1735812 : Nat := 4983230072969 + 3 ^ 40 * 1735812 * 2
def baseEnd_1735812 : Nat := 396135947485452382785401

theorem tailTrace_1735812 : CollatzResearch.WordTrace tailWord_1735812 prefixEnd_1735812 396135947485452382785401 := by
  unfold tailWord_1735812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31655132393728525966436845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42206843191638034621915793 31655132393728525966436845)
  ·
    refine ⟨11870674647648197237413817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31655132393728525966436845 11870674647648197237413817)
    ·
      refine ⟨8903005985736147928060363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11870674647648197237413817 8903005985736147928060363)
      ·
        refine ⟨13354508978604221892090545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8903005985736147928060363 13354508978604221892090545)
        ·
          refine ⟨10015881733953166419067909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13354508978604221892090545 10015881733953166419067909)
          ·
            refine ⟨1877977825116218703575233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10015881733953166419067909 1877977825116218703575233)
            ·
              refine ⟨1408483368837164027681425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877977825116218703575233 1408483368837164027681425)
              ·
                refine ⟨1056362526627873020761069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408483368837164027681425 1056362526627873020761069)
                ·
                  refine ⟨396135947485452382785401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056362526627873020761069 396135947485452382785401)
                  ·
                    rfl

theorem cell21_1735812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_1735812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735812 prefixEnd_1735812 := by exact prefixLift 1735812
  have htrace : WordTrace (prefixWord ++ tailWord_1735812) baseStart_1735812 baseEnd_1735812 := by
    simpa [prefixWord, tailWord_1735812, baseEnd_1735812] using wordTrace_append hprefix tailTrace_1735812
  have hstable : (prefixWord ++ tailWord_1735812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735812).length < 2 ^ (prefixWord ++ tailWord_1735812).sum := by decide
  have hdescent : baseEnd_1735812 < baseStart_1735812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735820 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_1735820 : Nat := 118140960795 + 1735820 * 2 ^ 59
def prefixEnd_1735820 : Nat := 4983230072969 + 3 ^ 40 * 1735820 * 2
def baseEnd_1735820 : Nat := 396137773194446146652051

theorem tailTrace_1735820 : CollatzResearch.WordTrace tailWord_1735820 prefixEnd_1735820 396137773194446146652051 := by
  unfold tailWord_1735820
  simp only [CollatzResearch.WordTrace]
  refine ⟨31655278285714034649582457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42207037714285379532776609 31655278285714034649582457)
  ·
    refine ⟨23741458714285525987186843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31655278285714034649582457 23741458714285525987186843)
    ·
      refine ⟨35612188071428288980780265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23741458714285525987186843 35612188071428288980780265)
      ·
        refine ⟨26709141053571216735585199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35612188071428288980780265 26709141053571216735585199)
        ·
          refine ⟨40063711580356825103377799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26709141053571216735585199 40063711580356825103377799)
          ·
            refine ⟨60095567370535237655066699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40063711580356825103377799 60095567370535237655066699)
            ·
              refine ⟨90143351055802856482600049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60095567370535237655066699 90143351055802856482600049)
              ·
                refine ⟨67607513291852142361950037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90143351055802856482600049 67607513291852142361950037)
                ·
                  refine ⟨396137773194446146652051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67607513291852142361950037 396137773194446146652051)
                  ·
                    rfl

theorem cell21_1735820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_1735820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735820 prefixEnd_1735820 := by exact prefixLift 1735820
  have htrace : WordTrace (prefixWord ++ tailWord_1735820) baseStart_1735820 baseEnd_1735820 := by
    simpa [prefixWord, tailWord_1735820, baseEnd_1735820] using wordTrace_append hprefix tailTrace_1735820
  have hstable : (prefixWord ++ tailWord_1735820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735820).length < 2 ^ (prefixWord ++ tailWord_1735820).sum := by decide
  have hdescent : baseEnd_1735820 < baseStart_1735820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735837 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 5]
def baseStart_1735837 : Nat := 118140960795 + 1735837 * 2 ^ 59
def prefixEnd_1735837 : Nat := 4983230072969 + 3 ^ 40 * 1735837 * 2
def baseEnd_1735837 : Nat := 396141652826057894868683

theorem tailTrace_1735837 : CollatzResearch.WordTrace tailWord_1735837 prefixEnd_1735837 396141652826057894868683 := by
  unfold tailWord_1735837
  simp only [CollatzResearch.WordTrace]
  refine ⟨63311176612366481202533765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42207451074910987468355843 63311176612366481202533765)
  ·
    refine ⟨11870845614818715225475081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63311176612366481202533765 11870845614818715225475081)
    ·
      refine ⟨8903134211114036419106311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11870845614818715225475081 8903134211114036419106311)
      ·
        refine ⟨13354701316671054628659467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8903134211114036419106311 13354701316671054628659467)
        ·
          refine ⟨20032051975006581942989201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13354701316671054628659467 20032051975006581942989201)
          ·
            refine ⟨15024038981254936457241901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20032051975006581942989201 15024038981254936457241901)
            ·
              refine ⟨5634014617970601171465713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15024038981254936457241901 5634014617970601171465713)
              ·
                refine ⟨4225510963477950878599285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5634014617970601171465713 4225510963477950878599285)
                ·
                  refine ⟨396141652826057894868683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4225510963477950878599285 396141652826057894868683)
                  ·
                    rfl

theorem cell21_1735837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_1735837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735837 prefixEnd_1735837 := by exact prefixLift 1735837
  have htrace : WordTrace (prefixWord ++ tailWord_1735837) baseStart_1735837 baseEnd_1735837 := by
    simpa [prefixWord, tailWord_1735837, baseEnd_1735837] using wordTrace_append hprefix tailTrace_1735837
  have hstable : (prefixWord ++ tailWord_1735837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735837).length < 2 ^ (prefixWord ++ tailWord_1735837).sum := by decide
  have hdescent : baseEnd_1735837 < baseStart_1735837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735868 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_1735868 : Nat := 118140960795 + 1735868 * 2 ^ 59
def prefixEnd_1735868 : Nat := 4983230072969 + 3 ^ 40 * 1735868 * 2
def baseEnd_1735868 : Nat := 396148727448408729851953

theorem tailTrace_1735868 : CollatzResearch.WordTrace tailWord_1735868 prefixEnd_1735868 396148727448408729851953 := by
  unfold tailWord_1735868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31656153637627086748456129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42208204850169448997941505 31656153637627086748456129)
  ·
    refine ⟨23742115228220315061342097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31656153637627086748456129 23742115228220315061342097)
    ·
      refine ⟨17806586421165236296006573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23742115228220315061342097 17806586421165236296006573)
      ·
        refine ⟨6677469907936963611002465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17806586421165236296006573 6677469907936963611002465)
        ·
          refine ⟨5008102430952722708251849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6677469907936963611002465 5008102430952722708251849)
          ·
            refine ⟨3756076823214542031188887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5008102430952722708251849 3756076823214542031188887)
            ·
              refine ⟨5634115234821813046783331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3756076823214542031188887 5634115234821813046783331)
              ·
                refine ⟨8451172852232719570174997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5634115234821813046783331 8451172852232719570174997)
                ·
                  refine ⟨396148727448408729851953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8451172852232719570174997 396148727448408729851953)
                  ·
                    rfl

theorem cell21_1735868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_1735868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735868 prefixEnd_1735868 := by exact prefixLift 1735868
  have htrace : WordTrace (prefixWord ++ tailWord_1735868) baseStart_1735868 baseEnd_1735868 := by
    simpa [prefixWord, tailWord_1735868, baseEnd_1735868] using wordTrace_append hprefix tailTrace_1735868
  have hstable : (prefixWord ++ tailWord_1735868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735868).length < 2 ^ (prefixWord ++ tailWord_1735868).sum := by decide
  have hdescent : baseEnd_1735868 < baseStart_1735868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1735981 : List Nat := [1, 5, 3, 1, 1, 3, 2, 2, 3]
def baseStart_1735981 : Nat := 118140960795 + 1735981 * 2 ^ 59
def prefixEnd_1735981 : Nat := 4983230072969 + 3 ^ 40 * 1735981 * 2
def baseEnd_1735981 : Nat := 396174515587945644468389

theorem tailTrace_1735981 : CollatzResearch.WordTrace tailWord_1735981 prefixEnd_1735981 396174515587945644468389 := by
  unfold tailWord_1735981
  simp only [CollatzResearch.WordTrace]
  refine ⟨63316428723844793795775797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42210952482563195863850531 63316428723844793795775797)
  ·
    refine ⟨5935915192860449418353981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63316428723844793795775797 5935915192860449418353981)
    ·
      refine ⟨2225968197322668531882743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5935915192860449418353981 2225968197322668531882743)
      ·
        refine ⟨3338952295984002797824115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225968197322668531882743 3338952295984002797824115)
        ·
          refine ⟨5008428443976004196736173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3338952295984002797824115 5008428443976004196736173)
          ·
            refine ⟨1878160666491001573776065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5008428443976004196736173 1878160666491001573776065)
            ·
              refine ⟨1408620499868251180332049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878160666491001573776065 1408620499868251180332049)
              ·
                refine ⟨1056465374901188385249037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408620499868251180332049 1056465374901188385249037)
                ·
                  refine ⟨396174515587945644468389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056465374901188385249037 396174515587945644468389)
                  ·
                    rfl

theorem cell21_1735981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_1735981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1735981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1735981 prefixEnd_1735981 := by exact prefixLift 1735981
  have htrace : WordTrace (prefixWord ++ tailWord_1735981) baseStart_1735981 baseEnd_1735981 := by
    simpa [prefixWord, tailWord_1735981, baseEnd_1735981] using wordTrace_append hprefix tailTrace_1735981
  have hstable : (prefixWord ++ tailWord_1735981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1735981).length < 2 ^ (prefixWord ++ tailWord_1735981).sum := by decide
  have hdescent : baseEnd_1735981 < baseStart_1735981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1735981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736034 : List Nat := [3, 3, 2, 1, 1, 1, 10]
def baseStart_1736034 : Nat := 118140960795 + 1736034 * 2 ^ 59
def prefixEnd_1736034 : Nat := 4983230072969 + 3 ^ 40 * 1736034 * 2
def baseEnd_1736034 : Nat := 44020734545558814453883

theorem tailTrace_1736034 : CollatzResearch.WordTrace tailWord_1736034 prefixEnd_1736034 44020734545558814453883 := by
  unfold tailWord_1736034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15829590448163195961863789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42212241195101855898303437 15829590448163195961863789)
  ·
    refine ⟨5936096418061198485698921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15829590448163195961863789 5936096418061198485698921)
    ·
      refine ⟨4452072313545898864274191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5936096418061198485698921 4452072313545898864274191)
      ·
        refine ⟨6678108470318848296411287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4452072313545898864274191 6678108470318848296411287)
        ·
          refine ⟨10017162705478272444616931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6678108470318848296411287 10017162705478272444616931)
          ·
            refine ⟨15025744058217408666925397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10017162705478272444616931 15025744058217408666925397)
            ·
              refine ⟨44020734545558814453883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15025744058217408666925397 44020734545558814453883)
              ·
                rfl

theorem cell21_1736034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 10].length) (baseStart_1736034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736034 prefixEnd_1736034 := by exact prefixLift 1736034
  have htrace : WordTrace (prefixWord ++ tailWord_1736034) baseStart_1736034 baseEnd_1736034 := by
    simpa [prefixWord, tailWord_1736034, baseEnd_1736034] using wordTrace_append hprefix tailTrace_1736034
  have hstable : (prefixWord ++ tailWord_1736034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736034).length < 2 ^ (prefixWord ++ tailWord_1736034).sum := by decide
  have hdescent : baseEnd_1736034 < baseStart_1736034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736186 : List Nat := [3, 1, 1, 1, 1, 2, 7, 5]
def baseStart_1736186 : Nat := 118140960795 + 1736186 * 2 ^ 59
def prefixEnd_1736186 : Nat := 4983230072969 + 3 ^ 40 * 1736186 * 2
def baseEnd_1736186 : Nat := 132073766460303614517101

theorem tailTrace_1736186 : CollatzResearch.WordTrace tailWord_1736186 prefixEnd_1736186 132073766460303614517101 := by
  unfold tailWord_1736186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15830976422025528451747103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42215937125401409204658941 15830976422025528451747103)
  ·
    refine ⟨23746464633038292677620655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15830976422025528451747103 23746464633038292677620655)
    ·
      refine ⟨35619696949557439016430983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23746464633038292677620655 35619696949557439016430983)
      ·
        refine ⟨53429545424336158524646475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35619696949557439016430983 53429545424336158524646475)
        ·
          refine ⟨80144318136504237786969713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53429545424336158524646475 80144318136504237786969713)
          ·
            refine ⟨60108238602378178340227285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80144318136504237786969713 60108238602378178340227285)
            ·
              refine ⟨1408786842243238554849077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60108238602378178340227285 1408786842243238554849077)
              ·
                refine ⟨132073766460303614517101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1408786842243238554849077 132073766460303614517101)
                ·
                  rfl

theorem cell21_1736186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_1736186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736186 prefixEnd_1736186 := by exact prefixLift 1736186
  have htrace : WordTrace (prefixWord ++ tailWord_1736186) baseStart_1736186 baseEnd_1736186 := by
    simpa [prefixWord, tailWord_1736186, baseEnd_1736186] using wordTrace_append hprefix tailTrace_1736186
  have hstable : (prefixWord ++ tailWord_1736186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736186).length < 2 ^ (prefixWord ++ tailWord_1736186).sum := by decide
  have hdescent : baseEnd_1736186 < baseStart_1736186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736206 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_1736206 : Nat := 118140960795 + 1736206 * 2 ^ 59
def prefixEnd_1736206 : Nat := 4983230072969 + 3 ^ 40 * 1736206 * 2
def baseEnd_1736206 : Nat := 396225863653395253217929

theorem tailTrace_1736206 : CollatzResearch.WordTrace tailWord_1736206 prefixEnd_1736206 396225863653395253217929 := by
  unfold tailWord_1736206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7915579393503707152839559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42216423432019771481810981 7915579393503707152839559)
  ·
    refine ⟨11873369090255560729259339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7915579393503707152839559 11873369090255560729259339)
    ·
      refine ⟨17810053635383341093889009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11873369090255560729259339 17810053635383341093889009)
      ·
        refine ⟨13357540226537505820416757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17810053635383341093889009 13357540226537505820416757)
        ·
          refine ⟨1252269396237891170664071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13357540226537505820416757 1252269396237891170664071)
          ·
            refine ⟨1878404094356836755996107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252269396237891170664071 1878404094356836755996107)
            ·
              refine ⟨2817606141535255133994161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878404094356836755996107 2817606141535255133994161)
              ·
                refine ⟨2113204606151441350495621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2817606141535255133994161 2113204606151441350495621)
                ·
                  refine ⟨396225863653395253217929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113204606151441350495621 396225863653395253217929)
                  ·
                    rfl

theorem cell21_1736206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_1736206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736206 prefixEnd_1736206 := by exact prefixLift 1736206
  have htrace : WordTrace (prefixWord ++ tailWord_1736206) baseStart_1736206 baseEnd_1736206 := by
    simpa [prefixWord, tailWord_1736206, baseEnd_1736206] using wordTrace_append hprefix tailTrace_1736206
  have hstable : (prefixWord ++ tailWord_1736206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736206).length < 2 ^ (prefixWord ++ tailWord_1736206).sum := by decide
  have hdescent : baseEnd_1736206 < baseStart_1736206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736321 : List Nat := [1, 2, 4, 2, 1, 11]
def baseStart_1736321 : Nat := 118140960795 + 1736321 * 2 ^ 59
def prefixEnd_1736321 : Nat := 4983230072969 + 3 ^ 40 * 1736321 * 2
def baseEnd_1736321 : Nat := 14676004008154837363001

theorem tailTrace_1736321 : CollatzResearch.WordTrace tailWord_1736321 prefixEnd_1736321 14676004008154837363001 := by
  unfold tailWord_1736321
  simp only [CollatzResearch.WordTrace]
  refine ⟨63328829542613031863152817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42219219695075354575435211 63328829542613031863152817)
  ·
    refine ⟨47496622156959773897364613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63328829542613031863152817 47496622156959773897364613)
    ·
      refine ⟨8905616654429957605755865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47496622156959773897364613 8905616654429957605755865)
      ·
        refine ⟨6679212490822468204316899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8905616654429957605755865 6679212490822468204316899)
        ·
          refine ⟨10018818736233702306475349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6679212490822468204316899 10018818736233702306475349)
          ·
            refine ⟨14676004008154837363001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10018818736233702306475349 14676004008154837363001)
            ·
              rfl

theorem cell21_1736321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 11].length) (baseStart_1736321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736321 prefixEnd_1736321 := by exact prefixLift 1736321
  have htrace : WordTrace (prefixWord ++ tailWord_1736321) baseStart_1736321 baseEnd_1736321 := by
    simpa [prefixWord, tailWord_1736321, baseEnd_1736321] using wordTrace_append hprefix tailTrace_1736321
  have hstable : (prefixWord ++ tailWord_1736321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736321).length < 2 ^ (prefixWord ++ tailWord_1736321).sum := by decide
  have hdescent : baseEnd_1736321 < baseStart_1736321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736327 : List Nat := [1, 1, 4, 2, 1, 5, 2, 2, 3]
def baseStart_1736327 : Nat := 118140960795 + 1736327 * 2 ^ 59
def prefixEnd_1736327 : Nat := 4983230072969 + 3 ^ 40 * 1736327 * 2
def baseEnd_1736327 : Nat := 396253477501925931701015

theorem tailTrace_1736327 : CollatzResearch.WordTrace tailWord_1736327 prefixEnd_1736327 396253477501925931701015 := by
  unfold tailWord_1736327
  simp only [CollatzResearch.WordTrace]
  refine ⟨63329048380591294887871235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42219365587060863258580823 63329048380591294887871235)
  ·
    refine ⟨94993572570886942331806853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63329048380591294887871235 94993572570886942331806853)
    ·
      refine ⟨17811294857041301687213785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94993572570886942331806853 17811294857041301687213785)
      ·
        refine ⟨13358471142780976265410339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17811294857041301687213785 13358471142780976265410339)
        ·
          refine ⟨20037706714171464398115509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13358471142780976265410339 20037706714171464398115509)
          ·
            refine ⟨1878535004453574787323329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20037706714171464398115509 1878535004453574787323329)
            ·
              refine ⟨1408901253340181090492497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878535004453574787323329 1408901253340181090492497)
              ·
                refine ⟨1056675940005135817869373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408901253340181090492497 1056675940005135817869373)
                ·
                  refine ⟨396253477501925931701015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056675940005135817869373 396253477501925931701015)
                  ·
                    rfl

theorem cell21_1736327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 3].length) (baseStart_1736327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736327 prefixEnd_1736327 := by exact prefixLift 1736327
  have htrace : WordTrace (prefixWord ++ tailWord_1736327) baseStart_1736327 baseEnd_1736327 := by
    simpa [prefixWord, tailWord_1736327, baseEnd_1736327] using wordTrace_append hprefix tailTrace_1736327
  have hstable : (prefixWord ++ tailWord_1736327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736327).length < 2 ^ (prefixWord ++ tailWord_1736327).sum := by decide
  have hdescent : baseEnd_1736327 < baseStart_1736327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736352 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_1736352 : Nat := 118140960795 + 1736352 * 2 ^ 59
def prefixEnd_1736352 : Nat := 4983230072969 + 3 ^ 40 * 1736352 * 2
def baseEnd_1736352 : Nat := 396259182842531443784297

theorem tailTrace_1736352 : CollatzResearch.WordTrace tailWord_1736352 prefixEnd_1736352 396259182842531443784297 := by
  unfold tailWord_1736352
  simp only [CollatzResearch.WordTrace]
  refine ⟨31664980102750362078765655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42219973470333816105020873 31664980102750362078765655)
  ·
    refine ⟨47497470154125543118148483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31664980102750362078765655 47497470154125543118148483)
    ·
      refine ⟨71246205231188314677222725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47497470154125543118148483 71246205231188314677222725)
      ·
        refine ⟨13358663480847809001979261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71246205231188314677222725 13358663480847809001979261)
        ·
          refine ⟨5009498805317928375742223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13358663480847809001979261 5009498805317928375742223)
          ·
            refine ⟨7514248207976892563613335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009498805317928375742223 7514248207976892563613335)
            ·
              refine ⟨11271372311965338845420003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7514248207976892563613335 11271372311965338845420003)
              ·
                refine ⟨16907058467948008268130005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11271372311965338845420003 16907058467948008268130005)
                ·
                  refine ⟨396259182842531443784297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16907058467948008268130005 396259182842531443784297)
                  ·
                    rfl

theorem cell21_1736352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_1736352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736352 prefixEnd_1736352 := by exact prefixLift 1736352
  have htrace : WordTrace (prefixWord ++ tailWord_1736352) baseStart_1736352 baseEnd_1736352 := by
    simpa [prefixWord, tailWord_1736352, baseEnd_1736352] using wordTrace_append hprefix tailTrace_1736352
  have hstable : (prefixWord ++ tailWord_1736352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736352).length < 2 ^ (prefixWord ++ tailWord_1736352).sum := by decide
  have hdescent : baseEnd_1736352 < baseStart_1736352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736406 : List Nat := [5, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1736406 : Nat := 118140960795 + 1736406 * 2 ^ 59
def prefixEnd_1736406 : Nat := 4983230072969 + 3 ^ 40 * 1736406 * 2
def baseEnd_1736406 : Nat := 132090502126079783294729

theorem tailTrace_1736406 : CollatzResearch.WordTrace tailWord_1736406 prefixEnd_1736406 132090502126079783294729 := by
  unfold tailWord_1736406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3958245609206568211249817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42221286498203394253331381 3958245609206568211249817)
  ·
    refine ⟨2968684206904926158437363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3958245609206568211249817 2968684206904926158437363)
    ·
      refine ⟨4453026310357389237656045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2968684206904926158437363 4453026310357389237656045)
      ·
        refine ⟨1669884866384020964121017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4453026310357389237656045 1669884866384020964121017)
        ·
          refine ⟨1252413649788015723090763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1669884866384020964121017 1252413649788015723090763)
          ·
            refine ⟨1878620474682023584636145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252413649788015723090763 1878620474682023584636145)
            ·
              refine ⟨1408965356011517688477109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878620474682023584636145 1408965356011517688477109)
              ·
                refine ⟨132090502126079783294729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1408965356011517688477109 132090502126079783294729)
                ·
                  rfl

theorem cell21_1736406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1736406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736406 prefixEnd_1736406 := by exact prefixLift 1736406
  have htrace : WordTrace (prefixWord ++ tailWord_1736406) baseStart_1736406 baseEnd_1736406 := by
    simpa [prefixWord, tailWord_1736406, baseEnd_1736406] using wordTrace_append hprefix tailTrace_1736406
  have hstable : (prefixWord ++ tailWord_1736406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736406).length < 2 ^ (prefixWord ++ tailWord_1736406).sum := by decide
  have hdescent : baseEnd_1736406 < baseStart_1736406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736580 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1736580 : Nat := 118140960795 + 1736580 * 2 ^ 59
def prefixEnd_1736580 : Nat := 4983230072969 + 3 ^ 40 * 1736580 * 2
def baseEnd_1736580 : Nat := 396311215548853713983831

theorem tailTrace_1736580 : CollatzResearch.WordTrace tailWord_1736580 prefixEnd_1736580 396311215548853713983831 := by
  unfold tailWord_1736580
  simp only [CollatzResearch.WordTrace]
  refine ⟨31669138024337359548415597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42225517365783146064554129 31669138024337359548415597)
  ·
    refine ⟨11875926759126509830655849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31669138024337359548415597 11875926759126509830655849)
    ·
      refine ⟨8906945069344882372991887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11875926759126509830655849 8906945069344882372991887)
      ·
        refine ⟨13360417604017323559487831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8906945069344882372991887 13360417604017323559487831)
        ·
          refine ⟨20040626406025985339231747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13360417604017323559487831 20040626406025985339231747)
          ·
            refine ⟨30060939609038978008847621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20040626406025985339231747 30060939609038978008847621)
            ·
              refine ⟨5636426176694808376658929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30060939609038978008847621 5636426176694808376658929)
              ·
                refine ⟨4227319632521106282494197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5636426176694808376658929 4227319632521106282494197)
                ·
                  refine ⟨396311215548853713983831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4227319632521106282494197 396311215548853713983831)
                  ·
                    rfl

theorem cell21_1736580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1736580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736580 prefixEnd_1736580 := by exact prefixLift 1736580
  have htrace : WordTrace (prefixWord ++ tailWord_1736580) baseStart_1736580 baseEnd_1736580 := by
    simpa [prefixWord, tailWord_1736580, baseEnd_1736580] using wordTrace_append hprefix tailTrace_1736580
  have hstable : (prefixWord ++ tailWord_1736580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736580).length < 2 ^ (prefixWord ++ tailWord_1736580).sum := by decide
  have hdescent : baseEnd_1736580 < baseStart_1736580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736583 : List Nat := [1, 1, 4, 2, 4, 2, 2, 5]
def baseStart_1736583 : Nat := 118140960795 + 1736583 * 2 ^ 59
def prefixEnd_1736583 : Nat := 4983230072969 + 3 ^ 40 * 1736583 * 2
def baseEnd_1736583 : Nat := 132103966729908791811275

theorem tailTrace_1736583 : CollatzResearch.WordTrace tailWord_1736583 prefixEnd_1736583 132103966729908791811275 := by
  unfold tailWord_1736583
  simp only [CollatzResearch.WordTrace]
  refine ⟨63338385467663850609190403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42225590311775900406126935 63338385467663850609190403)
  ·
    refine ⟨95007578201495775913785605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63338385467663850609190403 95007578201495775913785605)
    ·
      refine ⟨17813920912780457983834801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95007578201495775913785605 17813920912780457983834801)
      ·
        refine ⟨13360440684585343487876101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17813920912780457983834801 13360440684585343487876101)
        ·
          refine ⟨2505082628359751903976769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13360440684585343487876101 2505082628359751903976769)
          ·
            refine ⟨1878811971269813927982577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2505082628359751903976769 1878811971269813927982577)
            ·
              refine ⟨1409108978452360445986933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878811971269813927982577 1409108978452360445986933)
              ·
                refine ⟨132103966729908791811275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1409108978452360445986933 132103966729908791811275)
                ·
                  rfl

theorem cell21_1736583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 5].length) (baseStart_1736583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736583 prefixEnd_1736583 := by exact prefixLift 1736583
  have htrace : WordTrace (prefixWord ++ tailWord_1736583) baseStart_1736583 baseEnd_1736583 := by
    simpa [prefixWord, tailWord_1736583, baseEnd_1736583] using wordTrace_append hprefix tailTrace_1736583
  have hstable : (prefixWord ++ tailWord_1736583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736583).length < 2 ^ (prefixWord ++ tailWord_1736583).sum := by decide
  have hdescent : baseEnd_1736583 < baseStart_1736583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736625 : List Nat := [1, 2, 2, 4, 2, 1, 1, 8]
def baseStart_1736625 : Nat := 118140960795 + 1736625 * 2 ^ 59
def prefixEnd_1736625 : Nat := 4983230072969 + 3 ^ 40 * 1736625 * 2
def baseEnd_1736625 : Nat := 132107161720647878577913

theorem tailTrace_1736625 : CollatzResearch.WordTrace tailWord_1736625 prefixEnd_1736625 132107161720647878577913 := by
  unfold tailWord_1736625
  simp only [CollatzResearch.WordTrace]
  refine ⟨63339917333511691782219329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42226611555674461188146219 63339917333511691782219329)
  ·
    refine ⟨47504938000133768836664497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63339917333511691782219329 47504938000133768836664497)
    ·
      refine ⟨35628703500100326627498373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47504938000133768836664497 35628703500100326627498373)
      ·
        refine ⟨6680381906268811242655945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35628703500100326627498373 6680381906268811242655945)
        ·
          refine ⟨5010286429701608431991959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6680381906268811242655945 5010286429701608431991959)
          ·
            refine ⟨7515429644552412647987939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5010286429701608431991959 7515429644552412647987939)
            ·
              refine ⟨11273144466828618971981909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7515429644552412647987939 11273144466828618971981909)
              ·
                refine ⟨132107161720647878577913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11273144466828618971981909 132107161720647878577913)
                ·
                  rfl

theorem cell21_1736625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 8].length) (baseStart_1736625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736625 prefixEnd_1736625 := by exact prefixLift 1736625
  have htrace : WordTrace (prefixWord ++ tailWord_1736625) baseStart_1736625 baseEnd_1736625 := by
    simpa [prefixWord, tailWord_1736625, baseEnd_1736625] using wordTrace_append hprefix tailTrace_1736625
  have hstable : (prefixWord ++ tailWord_1736625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736625).length < 2 ^ (prefixWord ++ tailWord_1736625).sum := by decide
  have hdescent : baseEnd_1736625 < baseStart_1736625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736639 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 7]
def baseStart_1736639 : Nat := 118140960795 + 1736639 * 2 ^ 59
def prefixEnd_1736639 : Nat := 4983230072969 + 3 ^ 40 * 1736639 * 2
def baseEnd_1736639 : Nat := 396324680152682722500377

theorem tailTrace_1736639 : CollatzResearch.WordTrace tailWord_1736639 prefixEnd_1736639 396324680152682722500377 := by
  unfold tailWord_1736639
  simp only [CollatzResearch.WordTrace]
  refine ⟨63340427955460972173228971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42226951970307314782152647 63340427955460972173228971)
  ·
    refine ⟨95010641933191458259843457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63340427955460972173228971 95010641933191458259843457)
    ·
      refine ⟨71257981449893593694882593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95010641933191458259843457 71257981449893593694882593)
      ·
        refine ⟨53443486087420195271161945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71257981449893593694882593 53443486087420195271161945)
        ·
          refine ⟨40082614565565146453371459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53443486087420195271161945 40082614565565146453371459)
          ·
            refine ⟨60123921848347719680057189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40082614565565146453371459 60123921848347719680057189)
            ·
              refine ⟨11273235346565197440010723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60123921848347719680057189 11273235346565197440010723)
              ·
                refine ⟨16909853019847796160016085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11273235346565197440010723 16909853019847796160016085)
                ·
                  refine ⟨396324680152682722500377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16909853019847796160016085 396324680152682722500377)
                  ·
                    rfl

theorem cell21_1736639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_1736639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736639 prefixEnd_1736639 := by exact prefixLift 1736639
  have htrace : WordTrace (prefixWord ++ tailWord_1736639) baseStart_1736639 baseEnd_1736639 := by
    simpa [prefixWord, tailWord_1736639, baseEnd_1736639] using wordTrace_append hprefix tailTrace_1736639
  have hstable : (prefixWord ++ tailWord_1736639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736639).length < 2 ^ (prefixWord ++ tailWord_1736639).sum := by decide
  have hdescent : baseEnd_1736639 < baseStart_1736639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736715 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 7]
def baseStart_1736715 : Nat := 118140960795 + 1736715 * 2 ^ 59
def prefixEnd_1736715 : Nat := 4983230072969 + 3 ^ 40 * 1736715 * 2
def baseEnd_1736715 : Nat := 396342024388123479233555

theorem tailTrace_1736715 : CollatzResearch.WordTrace tailWord_1736715 prefixEnd_1736715 396342024388123479233555 := by
  unfold tailWord_1736715
  simp only [CollatzResearch.WordTrace]
  refine ⟨63343199903185637152995599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42228799935457091435330399 63343199903185637152995599)
  ·
    refine ⟨95014799854778455729493399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63343199903185637152995599 95014799854778455729493399)
    ·
      refine ⟨142522199782167683594240099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95014799854778455729493399 142522199782167683594240099)
      ·
        refine ⟨213783299673251525391360149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142522199782167683594240099 213783299673251525391360149)
        ·
          refine ⟨10021092172183665252720007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 213783299673251525391360149 10021092172183665252720007)
          ·
            refine ⟨15031638258275497879080011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10021092172183665252720007 15031638258275497879080011)
            ·
              refine ⟨22547457387413246818620017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15031638258275497879080011 22547457387413246818620017)
              ·
                refine ⟨16910593040559935113965013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22547457387413246818620017 16910593040559935113965013)
                ·
                  refine ⟨396342024388123479233555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16910593040559935113965013 396342024388123479233555)
                  ·
                    rfl

theorem cell21_1736715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_1736715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736715 prefixEnd_1736715 := by exact prefixLift 1736715
  have htrace : WordTrace (prefixWord ++ tailWord_1736715) baseStart_1736715 baseEnd_1736715 := by
    simpa [prefixWord, tailWord_1736715, baseEnd_1736715] using wordTrace_append hprefix tailTrace_1736715
  have hstable : (prefixWord ++ tailWord_1736715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736715).length < 2 ^ (prefixWord ++ tailWord_1736715).sum := by decide
  have hdescent : baseEnd_1736715 < baseStart_1736715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736732 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_1736732 : Nat := 118140960795 + 1736732 * 2 ^ 59
def prefixEnd_1736732 : Nat := 4983230072969 + 3 ^ 40 * 1736732 * 2
def baseEnd_1736732 : Nat := 396345904019735227450187

theorem tailTrace_1736732 : CollatzResearch.WordTrace tailWord_1736732 prefixEnd_1736732 396345904019735227450187 := by
  unfold tailWord_1736732
  simp only [CollatzResearch.WordTrace]
  refine ⟨31671909972062024528182225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42229213296082699370909633 31671909972062024528182225)
  ·
    refine ⟨23753932479046518396136669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31671909972062024528182225 23753932479046518396136669)
    ·
      refine ⟨8907724679642444398551251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23753932479046518396136669 8907724679642444398551251)
      ·
        refine ⟨13361587019463666597826877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8907724679642444398551251 13361587019463666597826877)
        ·
          refine ⟨5010595132298874974185079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13361587019463666597826877 5010595132298874974185079)
          ·
            refine ⟨7515892698448312461277619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5010595132298874974185079 7515892698448312461277619)
            ·
              refine ⟨11273839047672468691916429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7515892698448312461277619 11273839047672468691916429)
              ·
                refine ⟨4227689642877175759468661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11273839047672468691916429 4227689642877175759468661)
                ·
                  refine ⟨396345904019735227450187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4227689642877175759468661 396345904019735227450187)
                  ·
                    rfl

theorem cell21_1736732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_1736732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736732 prefixEnd_1736732 := by exact prefixLift 1736732
  have htrace : WordTrace (prefixWord ++ tailWord_1736732) baseStart_1736732 baseEnd_1736732 := by
    simpa [prefixWord, tailWord_1736732, baseEnd_1736732] using wordTrace_append hprefix tailTrace_1736732
  have hstable : (prefixWord ++ tailWord_1736732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736732).length < 2 ^ (prefixWord ++ tailWord_1736732).sum := by decide
  have hdescent : baseEnd_1736732 < baseStart_1736732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736797 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 4]
def baseStart_1736797 : Nat := 118140960795 + 1736797 * 2 ^ 59
def prefixEnd_1736797 : Nat := 4983230072969 + 3 ^ 40 * 1736797 * 2
def baseEnd_1736797 : Nat := 396360737905309558866721

theorem tailTrace_1736797 : CollatzResearch.WordTrace tailWord_1736797 prefixEnd_1736797 396360737905309558866721 := by
  unfold tailWord_1736797
  simp only [CollatzResearch.WordTrace]
  refine ⟨63346190688888565157480645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42230793792592376771653763 63346190688888565157480645)
  ·
    refine ⟨11877410754166605967027621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63346190688888565157480645 11877410754166605967027621)
    ·
      refine ⟨2227014516406238618817679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11877410754166605967027621 2227014516406238618817679)
      ·
        refine ⟨3340521774609357928226519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227014516406238618817679 3340521774609357928226519)
        ·
          refine ⟨5010782661914036892339779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3340521774609357928226519 5010782661914036892339779)
          ·
            refine ⟨7516173992871055338509669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5010782661914036892339779 7516173992871055338509669)
            ·
              refine ⟨1409282623663322875970563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7516173992871055338509669 1409282623663322875970563)
              ·
                refine ⟨2113923935494984313955845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409282623663322875970563 2113923935494984313955845)
                ·
                  refine ⟨396360737905309558866721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113923935494984313955845 396360737905309558866721)
                  ·
                    rfl

theorem cell21_1736797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_1736797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736797 prefixEnd_1736797 := by exact prefixLift 1736797
  have htrace : WordTrace (prefixWord ++ tailWord_1736797) baseStart_1736797 baseEnd_1736797 := by
    simpa [prefixWord, tailWord_1736797, baseEnd_1736797] using wordTrace_append hprefix tailTrace_1736797
  have hstable : (prefixWord ++ tailWord_1736797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736797).length < 2 ^ (prefixWord ++ tailWord_1736797).sum := by decide
  have hdescent : baseEnd_1736797 < baseStart_1736797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736842 : List Nat := [3, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_1736842 : Nat := 118140960795 + 1736842 * 2 ^ 59
def prefixEnd_1736842 : Nat := 4983230072969 + 3 ^ 40 * 1736842 * 2
def baseEnd_1736842 : Nat := 396371007518399480616629

theorem tailTrace_1736842 : CollatzResearch.WordTrace tailWord_1736842 prefixEnd_1736842 396371007518399480616629 := by
  unfold tailWord_1736842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15836957993431384460717195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42231887982483691895245853 15836957993431384460717195)
  ·
    refine ⟨23755436990147076691075793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15836957993431384460717195 23755436990147076691075793)
    ·
      refine ⟨17816577742610307518306845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23755436990147076691075793 17816577742610307518306845)
      ·
        refine ⟨6681216653478865319365067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17816577742610307518306845 6681216653478865319365067)
        ·
          refine ⟨10021824980218297979047601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6681216653478865319365067 10021824980218297979047601)
          ·
            refine ⟨7516368735163723484285701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10021824980218297979047601 7516368735163723484285701)
            ·
              refine ⟨1409319137843198153303569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7516368735163723484285701 1409319137843198153303569)
              ·
                refine ⟨1056989353382398614977677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409319137843198153303569 1056989353382398614977677)
                ·
                  refine ⟨396371007518399480616629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056989353382398614977677 396371007518399480616629)
                  ·
                    rfl

theorem cell21_1736842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_1736842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736842 prefixEnd_1736842 := by exact prefixLift 1736842
  have htrace : WordTrace (prefixWord ++ tailWord_1736842) baseStart_1736842 baseEnd_1736842 := by
    simpa [prefixWord, tailWord_1736842, baseEnd_1736842] using wordTrace_append hprefix tailTrace_1736842
  have hstable : (prefixWord ++ tailWord_1736842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736842).length < 2 ^ (prefixWord ++ tailWord_1736842).sum := by decide
  have hdescent : baseEnd_1736842 < baseStart_1736842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1736960 : List Nat := [2, 1, 1, 2, 1, 1, 4, 6, 3]
def baseStart_1736960 : Nat := 118140960795 + 1736960 * 2 ^ 59
def prefixEnd_1736960 : Nat := 4983230072969 + 3 ^ 40 * 1736960 * 2
def baseEnd_1736960 : Nat := 396397936726057497649721

theorem tailTrace_1736960 : CollatzResearch.WordTrace tailWord_1736960 prefixEnd_1736960 396397936726057497649721 := by
  unfold tailWord_1736960
  simp only [CollatzResearch.WordTrace]
  refine ⟨31676067893649021997832167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42234757191532029330442889 31676067893649021997832167)
  ·
    refine ⟨47514101840473532996748251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31676067893649021997832167 47514101840473532996748251)
    ·
      refine ⟨71271152760710299495122377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47514101840473532996748251 71271152760710299495122377)
      ·
        refine ⟨53453364570532724621341783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71271152760710299495122377 53453364570532724621341783)
        ·
          refine ⟨80180046855799086932012675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53453364570532724621341783 80180046855799086932012675)
          ·
            refine ⟨120270070283698630398019013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80180046855799086932012675 120270070283698630398019013)
            ·
              refine ⟨22550638178193493199628565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120270070283698630398019013 22550638178193493199628565)
              ·
                refine ⟨1057061164602819993732589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22550638178193493199628565 1057061164602819993732589)
                ·
                  refine ⟨396397936726057497649721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057061164602819993732589 396397936726057497649721)
                  ·
                    rfl

theorem cell21_1736960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_1736960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1736960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1736960 prefixEnd_1736960 := by exact prefixLift 1736960
  have htrace : WordTrace (prefixWord ++ tailWord_1736960) baseStart_1736960 baseEnd_1736960 := by
    simpa [prefixWord, tailWord_1736960, baseEnd_1736960] using wordTrace_append hprefix tailTrace_1736960
  have hstable : (prefixWord ++ tailWord_1736960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1736960).length < 2 ^ (prefixWord ++ tailWord_1736960).sum := by decide
  have hdescent : baseEnd_1736960 < baseStart_1736960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1736960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737005 : List Nat := [1, 5, 3, 1, 11]
def baseStart_1737005 : Nat := 118140960795 + 1737005 * 2 ^ 59
def prefixEnd_1737005 : Nat := 4983230072969 + 3 ^ 40 * 1737005 * 2
def baseEnd_1737005 : Nat := 4893928473322807646909

theorem tailTrace_1737005 : CollatzResearch.WordTrace tailWord_1737005 prefixEnd_1737005 4893928473322807646909 := by
  unfold tailWord_1737005
  simp only [CollatzResearch.WordTrace]
  refine ⟨63353777072135016681052469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42235851381423344454034979 63353777072135016681052469)
  ·
    refine ⟨5939416600512657813848669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63353777072135016681052469 5939416600512657813848669)
    ·
      refine ⟨2227281225192246680193251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5939416600512657813848669 2227281225192246680193251)
      ·
        refine ⟨3340921837788370020289877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227281225192246680193251 3340921837788370020289877)
        ·
          refine ⟨4893928473322807646909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3340921837788370020289877 4893928473322807646909)
          ·
            rfl

theorem cell21_1737005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 11].length) (baseStart_1737005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737005 prefixEnd_1737005 := by exact prefixLift 1737005
  have htrace : WordTrace (prefixWord ++ tailWord_1737005) baseStart_1737005 baseEnd_1737005 := by
    simpa [prefixWord, tailWord_1737005, baseEnd_1737005] using wordTrace_append hprefix tailTrace_1737005
  have hstable : (prefixWord ++ tailWord_1737005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737005).length < 2 ^ (prefixWord ++ tailWord_1737005).sum := by decide
  have hdescent : baseEnd_1737005 < baseStart_1737005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737022 : List Nat := [4, 2, 1, 2, 1, 4, 1, 6]
def baseStart_1737022 : Nat := 118140960795 + 1737022 * 2 ^ 59
def prefixEnd_1737022 : Nat := 4983230072969 + 3 ^ 40 * 1737022 * 2
def baseEnd_1737022 : Nat := 132137361990253055872087

theorem tailTrace_1737022 : CollatzResearch.WordTrace tailWord_1737022 prefixEnd_1737022 132137361990253055872087 := by
  unfold tailWord_1737022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919299639134178573052665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42236264742048952389614213 7919299639134178573052665)
  ·
    refine ⟨5939474729350633929789499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7919299639134178573052665 5939474729350633929789499)
    ·
      refine ⟨8909212094025950894684249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5939474729350633929789499 8909212094025950894684249)
      ·
        refine ⟨6681909070519463171013187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8909212094025950894684249 6681909070519463171013187)
        ·
          refine ⟨10022863605779194756519781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6681909070519463171013187 10022863605779194756519781)
          ·
            refine ⟨1879286926083599016847459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10022863605779194756519781 1879286926083599016847459)
            ·
              refine ⟨2818930389125398525271189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879286926083599016847459 2818930389125398525271189)
              ·
                refine ⟨132137361990253055872087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2818930389125398525271189 132137361990253055872087)
                ·
                  rfl

theorem cell21_1737022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_1737022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737022 prefixEnd_1737022 := by exact prefixLift 1737022
  have htrace : WordTrace (prefixWord ++ tailWord_1737022) baseStart_1737022 baseEnd_1737022 := by
    simpa [prefixWord, tailWord_1737022, baseEnd_1737022] using wordTrace_append hprefix tailTrace_1737022
  have hstable : (prefixWord ++ tailWord_1737022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737022).length < 2 ^ (prefixWord ++ tailWord_1737022).sum := by decide
  have hdescent : baseEnd_1737022 < baseStart_1737022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737033 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 8]
def baseStart_1737033 : Nat := 118140960795 + 1737033 * 2 ^ 59
def prefixEnd_1737033 : Nat := 4983230072969 + 3 ^ 40 * 1737033 * 2
def baseEnd_1737033 : Nat := 396414596320625592932905

theorem tailTrace_1737033 : CollatzResearch.WordTrace tailWord_1737033 prefixEnd_1737033 396414596320625592932905 := by
  unfold tailWord_1737033
  simp only [CollatzResearch.WordTrace]
  refine ⟨63354798316033577463071753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42236532210689051642047835 63354798316033577463071753)
  ·
    refine ⟨47516098737025183097303815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63354798316033577463071753 47516098737025183097303815)
    ·
      refine ⟨71274148105537774645955723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47516098737025183097303815 71274148105537774645955723)
      ·
        refine ⟨106911222158306661968933585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71274148105537774645955723 106911222158306661968933585)
        ·
          refine ⟨80183416618729996476700189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106911222158306661968933585 80183416618729996476700189)
          ·
            refine ⟨30068781232023748678762571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80183416618729996476700189 30068781232023748678762571)
            ·
              refine ⟨45103171848035623018143857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30068781232023748678762571 45103171848035623018143857)
              ·
                refine ⟨33827378886026717263607893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45103171848035623018143857 33827378886026717263607893)
                ·
                  refine ⟨396414596320625592932905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33827378886026717263607893 396414596320625592932905)
                  ·
                    rfl

theorem cell21_1737033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_1737033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737033 prefixEnd_1737033 := by exact prefixLift 1737033
  have htrace : WordTrace (prefixWord ++ tailWord_1737033) baseStart_1737033 baseEnd_1737033 := by
    simpa [prefixWord, tailWord_1737033, baseEnd_1737033] using wordTrace_append hprefix tailTrace_1737033
  have hstable : (prefixWord ++ tailWord_1737033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737033).length < 2 ^ (prefixWord ++ tailWord_1737033).sum := by decide
  have hdescent : baseEnd_1737033 < baseStart_1737033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737095 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 5]
def baseStart_1737095 : Nat := 118140960795 + 1737095 * 2 ^ 59
def prefixEnd_1737095 : Nat := 4983230072969 + 3 ^ 40 * 1737095 * 2
def baseEnd_1737095 : Nat := 396428745565327262899445

theorem tailTrace_1737095 : CollatzResearch.WordTrace tailWord_1737095 prefixEnd_1737095 396428745565327262899445 := by
  unfold tailWord_1737095
  simp only [CollatzResearch.WordTrace]
  refine ⟨63357059641808962051828739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42238039761205974701219159 63357059641808962051828739)
  ·
    refine ⟨95035589462713443077743109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63357059641808962051828739 95035589462713443077743109)
    ·
      refine ⟨17819173024258770577076833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95035589462713443077743109 17819173024258770577076833)
      ·
        refine ⟨13364379768194077932807625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17819173024258770577076833 13364379768194077932807625)
        ·
          refine ⟨10023284826145558449605719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13364379768194077932807625 10023284826145558449605719)
          ·
            refine ⟨15034927239218337674408579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10023284826145558449605719 15034927239218337674408579)
            ·
              refine ⟨22552390858827506511612869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15034927239218337674408579 22552390858827506511612869)
              ·
                refine ⟨4228573286030157470927413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22552390858827506511612869 4228573286030157470927413)
                ·
                  refine ⟨396428745565327262899445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4228573286030157470927413 396428745565327262899445)
                  ·
                    rfl

theorem cell21_1737095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_1737095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737095 prefixEnd_1737095 := by exact prefixLift 1737095
  have htrace : WordTrace (prefixWord ++ tailWord_1737095) baseStart_1737095 baseEnd_1737095 := by
    simpa [prefixWord, tailWord_1737095, baseEnd_1737095] using wordTrace_append hprefix tailTrace_1737095
  have hstable : (prefixWord ++ tailWord_1737095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737095).length < 2 ^ (prefixWord ++ tailWord_1737095).sum := by decide
  have hdescent : baseEnd_1737095 < baseStart_1737095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737098 : List Nat := [3, 1, 2, 5, 1, 1, 1, 7]
def baseStart_1737098 : Nat := 118140960795 + 1737098 * 2 ^ 59
def prefixEnd_1737098 : Nat := 4983230072969 + 3 ^ 40 * 1737098 * 2
def baseEnd_1737098 : Nat := 132143143402066641449813

theorem tailTrace_1737098 : CollatzResearch.WordTrace tailWord_1737098 prefixEnd_1737098 132143143402066641449813 := by
  unfold tailWord_1737098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15839292265199523391046987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42238112707198729042791965 15839292265199523391046987)
  ·
    refine ⟨23758938397799285086570481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15839292265199523391046987 23758938397799285086570481)
    ·
      refine ⟨17819203798349463814927861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23758938397799285086570481 17819203798349463814927861)
      ·
        refine ⟨1670550356095262232649487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17819203798349463814927861 1670550356095262232649487)
        ·
          refine ⟨2505825534142893348974231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670550356095262232649487 2505825534142893348974231)
          ·
            refine ⟨3758738301214340023461347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505825534142893348974231 3758738301214340023461347)
            ·
              refine ⟨5638107451821510035192021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758738301214340023461347 5638107451821510035192021)
              ·
                refine ⟨132143143402066641449813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5638107451821510035192021 132143143402066641449813)
                ·
                  rfl

theorem cell21_1737098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_1737098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737098 prefixEnd_1737098 := by exact prefixLift 1737098
  have htrace : WordTrace (prefixWord ++ tailWord_1737098) baseStart_1737098 baseEnd_1737098 := by
    simpa [prefixWord, tailWord_1737098, baseEnd_1737098] using wordTrace_append hprefix tailTrace_1737098
  have hstable : (prefixWord ++ tailWord_1737098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737098).length < 2 ^ (prefixWord ++ tailWord_1737098).sum := by decide
  have hdescent : baseEnd_1737098 < baseStart_1737098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737143 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 4]
def baseStart_1737143 : Nat := 118140960795 + 1737143 * 2 ^ 59
def prefixEnd_1737143 : Nat := 4983230072969 + 3 ^ 40 * 1737143 * 2
def baseEnd_1737143 : Nat := 396439699819289846099347

theorem tailTrace_1737143 : CollatzResearch.WordTrace tailWord_1737143 prefixEnd_1737143 396439699819289846099347 := by
  unfold tailWord_1737143
  simp only [CollatzResearch.WordTrace]
  refine ⟨63358810345635066249576083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42239206897090044166384055 63358810345635066249576083)
  ·
    refine ⟨95038215518452599374364125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63358810345635066249576083 95038215518452599374364125)
    ·
      refine ⟨35639330819419724765386547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95038215518452599374364125 35639330819419724765386547)
      ·
        refine ⟨53458996229129587148079821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35639330819419724765386547 53458996229129587148079821)
        ·
          refine ⟨20047123585923595180529933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53458996229129587148079821 20047123585923595180529933)
          ·
            refine ⟨7517671344721348192698725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20047123585923595180529933 7517671344721348192698725)
            ·
              refine ⟨1409563377135252786131011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7517671344721348192698725 1409563377135252786131011)
              ·
                refine ⟨2114345065702879179196517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409563377135252786131011 2114345065702879179196517)
                ·
                  refine ⟨396439699819289846099347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114345065702879179196517 396439699819289846099347)
                  ·
                    rfl

theorem cell21_1737143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 4].length) (baseStart_1737143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737143 prefixEnd_1737143 := by exact prefixLift 1737143
  have htrace : WordTrace (prefixWord ++ tailWord_1737143) baseStart_1737143 baseEnd_1737143 := by
    simpa [prefixWord, tailWord_1737143, baseEnd_1737143] using wordTrace_append hprefix tailTrace_1737143
  have hstable : (prefixWord ++ tailWord_1737143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737143).length < 2 ^ (prefixWord ++ tailWord_1737143).sum := by decide
  have hdescent : baseEnd_1737143 < baseStart_1737143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737205 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 5]
def baseStart_1737205 : Nat := 118140960795 + 1737205 * 2 ^ 59
def prefixEnd_1737205 : Nat := 4983230072969 + 3 ^ 40 * 1737205 * 2
def baseEnd_1737205 : Nat := 396453849063991516065887

theorem tailTrace_1737205 : CollatzResearch.WordTrace tailWord_1737205 prefixEnd_1737205 396453849063991516065887 := by
  unfold tailWord_1737205
  simp only [CollatzResearch.WordTrace]
  refine ⟨63361071671410450838333069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42240714447606967225555379 63361071671410450838333069)
  ·
    refine ⟨23760401876778919064374901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63361071671410450838333069 23760401876778919064374901)
    ·
      refine ⟨2227537675948023662285147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23760401876778919064374901 2227537675948023662285147)
      ·
        refine ⟨3341306513922035493427721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227537675948023662285147 3341306513922035493427721)
        ·
          refine ⟨2505979885441526620070791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3341306513922035493427721 2505979885441526620070791)
          ·
            refine ⟨3758969828162289930106187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505979885441526620070791 3758969828162289930106187)
            ·
              refine ⟨5638454742243434895159281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758969828162289930106187 5638454742243434895159281)
              ·
                refine ⟨4228841056682576171369461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5638454742243434895159281 4228841056682576171369461)
                ·
                  refine ⟨396453849063991516065887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4228841056682576171369461 396453849063991516065887)
                  ·
                    rfl

theorem cell21_1737205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_1737205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737205 prefixEnd_1737205 := by exact prefixLift 1737205
  have htrace : WordTrace (prefixWord ++ tailWord_1737205) baseStart_1737205 baseEnd_1737205 := by
    simpa [prefixWord, tailWord_1737205, baseEnd_1737205] using wordTrace_append hprefix tailTrace_1737205
  have hstable : (prefixWord ++ tailWord_1737205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737205).length < 2 ^ (prefixWord ++ tailWord_1737205).sum := by decide
  have hdescent : baseEnd_1737205 < baseStart_1737205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737236 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1737236 : Nat := 118140960795 + 1737236 * 2 ^ 59
def prefixEnd_1737236 : Nat := 4983230072969 + 3 ^ 40 * 1737236 * 2
def baseEnd_1737236 : Nat := 396460923686342351049157

theorem tailTrace_1737236 : CollatzResearch.WordTrace tailWord_1737236 prefixEnd_1737236 396460923686342351049157 := by
  unfold tailWord_1737236
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681101167149071566355781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42241468222865428755141041 31681101167149071566355781)
  ·
    refine ⟨5940206468840450918691709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31681101167149071566355781 5940206468840450918691709)
    ·
      refine ⟨2227577425815169094509391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5940206468840450918691709 2227577425815169094509391)
      ·
        refine ⟨3341366138722753641764087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227577425815169094509391 3341366138722753641764087)
        ·
          refine ⟨5012049208084130462646131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341366138722753641764087 5012049208084130462646131)
          ·
            refine ⟨7518073812126195693969197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012049208084130462646131 7518073812126195693969197)
            ·
              refine ⟨2819277679547323385238449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7518073812126195693969197 2819277679547323385238449)
              ·
                refine ⟨2114458259660492538928837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819277679547323385238449 2114458259660492538928837)
                ·
                  refine ⟨396460923686342351049157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114458259660492538928837 396460923686342351049157)
                  ·
                    rfl

theorem cell21_1737236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1737236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737236 prefixEnd_1737236 := by exact prefixLift 1737236
  have htrace : WordTrace (prefixWord ++ tailWord_1737236) baseStart_1737236 baseEnd_1737236 := by
    simpa [prefixWord, tailWord_1737236, baseEnd_1737236] using wordTrace_append hprefix tailTrace_1737236
  have hstable : (prefixWord ++ tailWord_1737236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737236).length < 2 ^ (prefixWord ++ tailWord_1737236).sum := by decide
  have hdescent : baseEnd_1737236 < baseStart_1737236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737281 : List Nat := [1, 2, 5, 1, 1, 2, 3, 3, 3]
def baseStart_1737281 : Nat := 118140960795 + 1737281 * 2 ^ 59
def prefixEnd_1737281 : Nat := 4983230072969 + 3 ^ 40 * 1737281 * 2
def baseEnd_1737281 : Nat := 396471193299432272799065

theorem tailTrace_1737281 : CollatzResearch.WordTrace tailWord_1737281 prefixEnd_1737281 396471193299432272799065 := by
  unfold tailWord_1737281
  simp only [CollatzResearch.WordTrace]
  refine ⟨63363843619135115818099697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42242562412756743878733131 63363843619135115818099697)
  ·
    refine ⟨47522882714351336863574773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63363843619135115818099697 47522882714351336863574773)
    ·
      refine ⟨4455270254470437830960135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47522882714351336863574773 4455270254470437830960135)
      ·
        refine ⟨6682905381705656746440203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4455270254470437830960135 6682905381705656746440203)
        ·
          refine ⟨10024358072558485119660305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682905381705656746440203 10024358072558485119660305)
          ·
            refine ⟨7518268554418863839745229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10024358072558485119660305 7518268554418863839745229)
            ·
              refine ⟨2819350707907073939904461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7518268554418863839745229 2819350707907073939904461)
              ·
                refine ⟨1057256515465152727464173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2819350707907073939904461 1057256515465152727464173)
                ·
                  refine ⟨396471193299432272799065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057256515465152727464173 396471193299432272799065)
                  ·
                    rfl

theorem cell21_1737281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_1737281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737281 prefixEnd_1737281 := by exact prefixLift 1737281
  have htrace : WordTrace (prefixWord ++ tailWord_1737281) baseStart_1737281 baseEnd_1737281 := by
    simpa [prefixWord, tailWord_1737281, baseEnd_1737281] using wordTrace_append hprefix tailTrace_1737281
  have hstable : (prefixWord ++ tailWord_1737281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737281).length < 2 ^ (prefixWord ++ tailWord_1737281).sum := by decide
  have hdescent : baseEnd_1737281 < baseStart_1737281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737284 : List Nat := [2, 3, 5, 1, 2, 1, 7]
def baseStart_1737284 : Nat := 118140960795 + 1737284 * 2 ^ 59
def prefixEnd_1737284 : Nat := 4983230072969 + 3 ^ 40 * 1737284 * 2
def baseEnd_1737284 : Nat := 44052430882256103805451

theorem tailTrace_1737284 : CollatzResearch.WordTrace tailWord_1737284 prefixEnd_1737284 44052430882256103805451 := by
  unfold tailWord_1737284
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681976519062123665229453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42242635358749498220305937 31681976519062123665229453)
  ·
    refine ⟨11880741194648296374461045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31681976519062123665229453 11880741194648296374461045)
    ·
      refine ⟨1113819486998277785105723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11880741194648296374461045 1113819486998277785105723)
      ·
        refine ⟨1670729230497416677658585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113819486998277785105723 1670729230497416677658585)
        ·
          refine ⟨1253046922873062508243939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670729230497416677658585 1253046922873062508243939)
          ·
            refine ⟨1879570384309593762365909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253046922873062508243939 1879570384309593762365909)
            ·
              refine ⟨44052430882256103805451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1879570384309593762365909 44052430882256103805451)
              ·
                rfl

theorem cell21_1737284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 7].length) (baseStart_1737284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737284 prefixEnd_1737284 := by exact prefixLift 1737284
  have htrace : WordTrace (prefixWord ++ tailWord_1737284) baseStart_1737284 baseEnd_1737284 := by
    simpa [prefixWord, tailWord_1737284, baseEnd_1737284] using wordTrace_append hprefix tailTrace_1737284
  have hstable : (prefixWord ++ tailWord_1737284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737284).length < 2 ^ (prefixWord ++ tailWord_1737284).sum := by decide
  have hdescent : baseEnd_1737284 < baseStart_1737284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737346 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1737346 : Nat := 118140960795 + 1737346 * 2 ^ 59
def prefixEnd_1737346 : Nat := 4983230072969 + 3 ^ 40 * 1737346 * 2
def baseEnd_1737346 : Nat := 396486027185006604215599

theorem tailTrace_1737346 : CollatzResearch.WordTrace tailWord_1737346 prefixEnd_1737346 396486027185006604215599 := by
  unfold tailWord_1737346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15841553590974907979803973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42244142909266421279477261 15841553590974907979803973)
  ·
    refine ⟨2970291298307795246213245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15841553590974907979803973 2970291298307795246213245)
    ·
      refine ⟨1113859236865423217329967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2970291298307795246213245 1113859236865423217329967)
      ·
        refine ⟨1670788855298134825994951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113859236865423217329967 1670788855298134825994951)
        ·
          refine ⟨2506183282947202238992427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670788855298134825994951 2506183282947202238992427)
          ·
            refine ⟨3759274924420803358488641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506183282947202238992427 3759274924420803358488641)
            ·
              refine ⟨2819456193315602518866481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3759274924420803358488641 2819456193315602518866481)
              ·
                refine ⟨2114592144986701889149861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819456193315602518866481 2114592144986701889149861)
                ·
                  refine ⟨396486027185006604215599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114592144986701889149861 396486027185006604215599)
                  ·
                    rfl

theorem cell21_1737346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1737346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737346 prefixEnd_1737346 := by exact prefixLift 1737346
  have htrace : WordTrace (prefixWord ++ tailWord_1737346) baseStart_1737346 baseEnd_1737346 := by
    simpa [prefixWord, tailWord_1737346, baseEnd_1737346] using wordTrace_append hprefix tailTrace_1737346
  have hstable : (prefixWord ++ tailWord_1737346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737346).length < 2 ^ (prefixWord ++ tailWord_1737346).sum := by decide
  have hdescent : baseEnd_1737346 < baseStart_1737346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737416 : List Nat := [2, 1, 3, 1, 2, 3, 2, 4, 3]
def baseStart_1737416 : Nat := 118140960795 + 1737416 * 2 ^ 59
def prefixEnd_1737416 : Nat := 4983230072969 + 3 ^ 40 * 1737416 * 2
def baseEnd_1737416 : Nat := 396502002138702038048789

theorem tailTrace_1737416 : CollatzResearch.WordTrace tailWord_1737416 prefixEnd_1737416 396502002138702038048789 := by
  unfold tailWord_1737416
  simp only [CollatzResearch.WordTrace]
  refine ⟨31684383736823016937132051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42245844982430689249509401 31684383736823016937132051)
  ·
    refine ⟨47526575605234525405698077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31684383736823016937132051 47526575605234525405698077)
    ·
      refine ⟨17822465851962947027136779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47526575605234525405698077 17822465851962947027136779)
      ·
        refine ⟨26733698777944420540705169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17822465851962947027136779 26733698777944420540705169)
        ·
          refine ⟨20050274083458315405528877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26733698777944420540705169 20050274083458315405528877)
          ·
            refine ⟨7518852781296868277073329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20050274083458315405528877 7518852781296868277073329)
            ·
              refine ⟨5639139585972651207804997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7518852781296868277073329 5639139585972651207804997)
              ·
                refine ⟨1057338672369872101463437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5639139585972651207804997 1057338672369872101463437)
                ·
                  refine ⟨396502002138702038048789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057338672369872101463437 396502002138702038048789)
                  ·
                    rfl

theorem cell21_1737416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_1737416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737416 prefixEnd_1737416 := by exact prefixLift 1737416
  have htrace : WordTrace (prefixWord ++ tailWord_1737416) baseStart_1737416 baseEnd_1737416 := by
    simpa [prefixWord, tailWord_1737416, baseEnd_1737416] using wordTrace_append hprefix tailTrace_1737416
  have hstable : (prefixWord ++ tailWord_1737416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737416).length < 2 ^ (prefixWord ++ tailWord_1737416).sum := by decide
  have hdescent : baseEnd_1737416 < baseStart_1737416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737444 : List Nat := [2, 3, 1, 1, 1, 5, 1, 7]
def baseStart_1737444 : Nat := 118140960795 + 1737444 * 2 ^ 59
def prefixEnd_1737444 : Nat := 4983230072969 + 3 ^ 40 * 1737444 * 2
def baseEnd_1737444 : Nat := 132169464040060070527355

theorem tailTrace_1737444 : CollatzResearch.WordTrace tailWord_1737444 prefixEnd_1737444 132169464040060070527355 := by
  unfold tailWord_1737444
  simp only [CollatzResearch.WordTrace]
  refine ⟨31684894358772297328141693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42246525811696396437522257 31684894358772297328141693)
  ·
    refine ⟨11881835384539611498053135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31684894358772297328141693 11881835384539611498053135)
    ·
      refine ⟨17822753076809417247079703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11881835384539611498053135 17822753076809417247079703)
      ·
        refine ⟨26734129615214125870619555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17822753076809417247079703 26734129615214125870619555)
        ·
          refine ⟨40101194422821188805929333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26734129615214125870619555 40101194422821188805929333)
          ·
            refine ⟨3759486977139486450555875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40101194422821188805929333 3759486977139486450555875)
            ·
              refine ⟨5639230465709229675833813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759486977139486450555875 5639230465709229675833813)
              ·
                refine ⟨132169464040060070527355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5639230465709229675833813 132169464040060070527355)
                ·
                  rfl

theorem cell21_1737444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_1737444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737444 prefixEnd_1737444 := by exact prefixLift 1737444
  have htrace : WordTrace (prefixWord ++ tailWord_1737444) baseStart_1737444 baseEnd_1737444 := by
    simpa [prefixWord, tailWord_1737444, baseEnd_1737444] using wordTrace_append hprefix tailTrace_1737444
  have hstable : (prefixWord ++ tailWord_1737444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737444).length < 2 ^ (prefixWord ++ tailWord_1737444).sum := by decide
  have hdescent : baseEnd_1737444 < baseStart_1737444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737526 : List Nat := [5, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1737526 : Nat := 118140960795 + 1737526 * 2 ^ 59
def prefixEnd_1737526 : Nat := 4983230072969 + 3 ^ 40 * 1737526 * 2
def baseEnd_1737526 : Nat := 396527105637366291215231

theorem tailTrace_1737526 : CollatzResearch.WordTrace tailWord_1737526 prefixEnd_1737526 396527105637366291215231 := by
  unfold tailWord_1737526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960798718952970166298027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42248519668831681773845621 3960798718952970166298027)
  ·
    refine ⟨5941198078429455249447041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3960798718952970166298027 5941198078429455249447041)
    ·
      refine ⟨4455898558822091437085281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5941198078429455249447041 4455898558822091437085281)
      ·
        refine ⟨3341923919116568577813961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4455898558822091437085281 3341923919116568577813961)
        ·
          refine ⟨2506442939337426433360471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3341923919116568577813961 2506442939337426433360471)
          ·
            refine ⟨3759664409006139650040707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506442939337426433360471 3759664409006139650040707)
            ·
              refine ⟨5639496613509209475061061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759664409006139650040707 5639496613509209475061061)
              ·
                refine ⟨1057405615032976776573949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5639496613509209475061061 1057405615032976776573949)
                ·
                  refine ⟨396527105637366291215231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057405615032976776573949 396527105637366291215231)
                  ·
                    rfl

theorem cell21_1737526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1737526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737526 prefixEnd_1737526 := by exact prefixLift 1737526
  have htrace : WordTrace (prefixWord ++ tailWord_1737526) baseStart_1737526 baseEnd_1737526 := by
    simpa [prefixWord, tailWord_1737526, baseEnd_1737526] using wordTrace_append hprefix tailTrace_1737526
  have hstable : (prefixWord ++ tailWord_1737526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737526).length < 2 ^ (prefixWord ++ tailWord_1737526).sum := by decide
  have hdescent : baseEnd_1737526 < baseStart_1737526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737568 : List Nat := [2, 1, 1, 3, 3, 1, 4, 3, 3]
def baseStart_1737568 : Nat := 118140960795 + 1737568 * 2 ^ 59
def prefixEnd_1737568 : Nat := 4983230072969 + 3 ^ 40 * 1737568 * 2
def baseEnd_1737568 : Nat := 396536690609583551515145

theorem tailTrace_1737568 : CollatzResearch.WordTrace tailWord_1737568 prefixEnd_1737568 396536690609583551515145 := by
  unfold tailWord_1737568
  simp only [CollatzResearch.WordTrace]
  refine ⟨31687155684547681916898679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42249540912730242555864905 31687155684547681916898679)
  ·
    refine ⟨47530733526821522875348019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31687155684547681916898679 47530733526821522875348019)
    ·
      refine ⟨71296100290232284313022029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47530733526821522875348019 71296100290232284313022029)
      ·
        refine ⟨26736037608837106617383261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71296100290232284313022029 26736037608837106617383261)
        ·
          refine ⟨10026014103313914981518723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26736037608837106617383261 10026014103313914981518723)
          ·
            refine ⟨15039021154970872472278085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10026014103313914981518723 15039021154970872472278085)
            ·
              refine ⟨2819816466557038588552141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15039021154970872472278085 2819816466557038588552141)
              ·
                refine ⟨1057431174958889470707053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2819816466557038588552141 1057431174958889470707053)
                ·
                  refine ⟨396536690609583551515145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057431174958889470707053 396536690609583551515145)
                  ·
                    rfl

theorem cell21_1737568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_1737568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737568 prefixEnd_1737568 := by exact prefixLift 1737568
  have htrace : WordTrace (prefixWord ++ tailWord_1737568) baseStart_1737568 baseEnd_1737568 := by
    simpa [prefixWord, tailWord_1737568, baseEnd_1737568] using wordTrace_append hprefix tailTrace_1737568
  have hstable : (prefixWord ++ tailWord_1737568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737568).length < 2 ^ (prefixWord ++ tailWord_1737568).sum := by decide
  have hdescent : baseEnd_1737568 < baseStart_1737568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737641 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 4]
def baseStart_1737641 : Nat := 118140960795 + 1737641 * 2 ^ 59
def prefixEnd_1737641 : Nat := 4983230072969 + 3 ^ 40 * 1737641 * 2
def baseEnd_1737641 : Nat := 396553350204151646798329

theorem tailTrace_1737641 : CollatzResearch.WordTrace tailWord_1737641 prefixEnd_1737641 396553350204151646798329 := by
  unfold tailWord_1737641
  simp only [CollatzResearch.WordTrace]
  refine ⟨63376973897830897301204777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42251315931887264867469851 63376973897830897301204777)
  ·
    refine ⟨47532730423373172975903583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63376973897830897301204777 47532730423373172975903583)
    ·
      refine ⟨71299095635059759463855375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47532730423373172975903583 71299095635059759463855375)
      ·
        refine ⟨106948643452589639195783063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71299095635059759463855375 106948643452589639195783063)
        ·
          refine ⟨160422965178884458793674595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106948643452589639195783063 160422965178884458793674595)
          ·
            refine ⟨240634447768326688190511893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160422965178884458793674595 240634447768326688190511893)
            ·
              refine ⟨11279739739140313508930245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 240634447768326688190511893 11279739739140313508930245)
              ·
                refine ⟨2114951201088808782924421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11279739739140313508930245 2114951201088808782924421)
                ·
                  refine ⟨396553350204151646798329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114951201088808782924421 396553350204151646798329)
                  ·
                    rfl

theorem cell21_1737641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_1737641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737641 prefixEnd_1737641 := by exact prefixLift 1737641
  have htrace : WordTrace (prefixWord ++ tailWord_1737641) baseStart_1737641 baseEnd_1737641 := by
    simpa [prefixWord, tailWord_1737641, baseEnd_1737641] using wordTrace_append hprefix tailTrace_1737641
  have hstable : (prefixWord ++ tailWord_1737641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737641).length < 2 ^ (prefixWord ++ tailWord_1737641).sum := by decide
  have hdescent : baseEnd_1737641 < baseStart_1737641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737655 : List Nat := [1, 1, 3, 1, 3, 1, 3, 8]
def baseStart_1737655 : Nat := 118140960795 + 1737655 * 2 ^ 59
def prefixEnd_1737655 : Nat := 4983230072969 + 3 ^ 40 * 1737655 * 2
def baseEnd_1737655 : Nat := 132185515064963577854989

theorem tailTrace_1737655 : CollatzResearch.WordTrace tailWord_1737655 prefixEnd_1737655 132185515064963577854989 := by
  unfold tailWord_1737655
  simp only [CollatzResearch.WordTrace]
  refine ⟨63377484519780177692214419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42251656346520118461476279 63377484519780177692214419)
  ·
    refine ⟨95066226779670266538321629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63377484519780177692214419 95066226779670266538321629)
    ·
      refine ⟨35649835042376349951870611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95066226779670266538321629 35649835042376349951870611)
      ·
        refine ⟨53474752563564524927805917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35649835042376349951870611 53474752563564524927805917)
        ·
          refine ⟨20053032211336696847927219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53474752563564524927805917 20053032211336696847927219)
          ·
            refine ⟨30079548317005045271890829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20053032211336696847927219 30079548317005045271890829)
            ·
              refine ⟨11279830618876891976959061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30079548317005045271890829 11279830618876891976959061)
              ·
                refine ⟨132185515064963577854989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11279830618876891976959061 132185515064963577854989)
                ·
                  rfl

theorem cell21_1737655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 8].length) (baseStart_1737655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737655 prefixEnd_1737655 := by exact prefixLift 1737655
  have htrace : WordTrace (prefixWord ++ tailWord_1737655) baseStart_1737655 baseEnd_1737655 := by
    simpa [prefixWord, tailWord_1737655, baseEnd_1737655] using wordTrace_append hprefix tailTrace_1737655
  have hstable : (prefixWord ++ tailWord_1737655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737655).length < 2 ^ (prefixWord ++ tailWord_1737655).sum := by decide
  have hdescent : baseEnd_1737655 < baseStart_1737655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737751 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 4]
def baseStart_1737751 : Nat := 118140960795 + 1737751 * 2 ^ 59
def prefixEnd_1737751 : Nat := 4983230072969 + 3 ^ 40 * 1737751 * 2
def baseEnd_1737751 : Nat := 396578453702815899964771

theorem tailTrace_1737751 : CollatzResearch.WordTrace tailWord_1737751 prefixEnd_1737751 396578453702815899964771 := by
  unfold tailWord_1737751
  simp only [CollatzResearch.WordTrace]
  refine ⟨63380985927432386087709107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42253990618288257391806071 63380985927432386087709107)
  ·
    refine ⟨95071478891148579131563661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63380985927432386087709107 95071478891148579131563661)
    ·
      refine ⟨35651804584180717174336373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95071478891148579131563661 35651804584180717174336373)
      ·
        refine ⟨3342356679766942235094035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35651804584180717174336373 3342356679766942235094035)
        ·
          refine ⟨5013535019650413352641053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342356679766942235094035 5013535019650413352641053)
          ·
            refine ⟨1880075632368905007240395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5013535019650413352641053 1880075632368905007240395)
            ·
              refine ⟨2820113448553357510860593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880075632368905007240395 2820113448553357510860593)
              ·
                refine ⟨2115085086415018133145445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2820113448553357510860593 2115085086415018133145445)
                ·
                  refine ⟨396578453702815899964771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2115085086415018133145445 396578453702815899964771)
                  ·
                    rfl

theorem cell21_1737751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 4].length) (baseStart_1737751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737751 prefixEnd_1737751 := by exact prefixLift 1737751
  have htrace : WordTrace (prefixWord ++ tailWord_1737751) baseStart_1737751 baseEnd_1737751 := by
    simpa [prefixWord, tailWord_1737751, baseEnd_1737751] using wordTrace_append hprefix tailTrace_1737751
  have hstable : (prefixWord ++ tailWord_1737751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737751).length < 2 ^ (prefixWord ++ tailWord_1737751).sum := by decide
  have hdescent : baseEnd_1737751 < baseStart_1737751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737782 : List Nat := [5, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1737782 : Nat := 118140960795 + 1737782 * 2 ^ 59
def prefixEnd_1737782 : Nat := 4983230072969 + 3 ^ 40 * 1737782 * 2
def baseEnd_1737782 : Nat := 132195176108388911649347

theorem tailTrace_1737782 : CollatzResearch.WordTrace tailWord_1737782 prefixEnd_1737782 132195176108388911649347 := by
  unfold tailWord_1737782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961382286895004898880475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42254744393546718921391733 3961382286895004898880475)
  ·
    refine ⟨5942073430342507348320713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3961382286895004898880475 5942073430342507348320713)
    ·
      refine ⟨4456555072756880511240535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5942073430342507348320713 4456555072756880511240535)
      ·
        refine ⟨6684832609135320766860803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456555072756880511240535 6684832609135320766860803)
        ·
          refine ⟨10027248913702981150291205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684832609135320766860803 10027248913702981150291205)
          ·
            refine ⟨1880109171319308965679601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10027248913702981150291205 1880109171319308965679601)
            ·
              refine ⟨1410081878489481724259701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880109171319308965679601 1410081878489481724259701)
              ·
                refine ⟨132195176108388911649347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1410081878489481724259701 132195176108388911649347)
                ·
                  rfl

theorem cell21_1737782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1737782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737782 prefixEnd_1737782 := by exact prefixLift 1737782
  have htrace : WordTrace (prefixWord ++ tailWord_1737782) baseStart_1737782 baseEnd_1737782 := by
    simpa [prefixWord, tailWord_1737782, baseEnd_1737782] using wordTrace_append hprefix tailTrace_1737782
  have hstable : (prefixWord ++ tailWord_1737782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737782).length < 2 ^ (prefixWord ++ tailWord_1737782).sum := by decide
  have hdescent : baseEnd_1737782 < baseStart_1737782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1737965 : List Nat := [1, 5, 1, 2, 2, 3, 1, 3, 3]
def baseStart_1737965 : Nat := 118140960795 + 1737965 * 2 ^ 59
def prefixEnd_1737965 : Nat := 4983230072969 + 3 ^ 40 * 1737965 * 2
def baseEnd_1737965 : Nat := 396627291418399083397667

theorem tailTrace_1737965 : CollatzResearch.WordTrace tailWord_1737965 prefixEnd_1737965 396627291418399083397667 := by
  unfold tailWord_1737965
  simp only [CollatzResearch.WordTrace]
  refine ⟨63388791148657100635999349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42259194099104733757332899 63388791148657100635999349)
  ·
    refine ⟨5942699170186603184624939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63388791148657100635999349 5942699170186603184624939)
    ·
      refine ⟨8914048755279904776937409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5942699170186603184624939 8914048755279904776937409)
      ·
        refine ⟨6685536566459928582703057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8914048755279904776937409 6685536566459928582703057)
        ·
          refine ⟨5014152424844946437027293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6685536566459928582703057 5014152424844946437027293)
          ·
            refine ⟨1880307159316854913885235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5014152424844946437027293 1880307159316854913885235)
            ·
              refine ⟨2820460738975282370827853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880307159316854913885235 2820460738975282370827853)
              ·
                refine ⟨1057672777115730889060445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2820460738975282370827853 1057672777115730889060445)
                ·
                  refine ⟨396627291418399083397667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057672777115730889060445 396627291418399083397667)
                  ·
                    rfl

theorem cell21_1737965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_1737965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1737965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1737965 prefixEnd_1737965 := by exact prefixLift 1737965
  have htrace : WordTrace (prefixWord ++ tailWord_1737965) baseStart_1737965 baseEnd_1737965 := by
    simpa [prefixWord, tailWord_1737965, baseEnd_1737965] using wordTrace_append hprefix tailTrace_1737965
  have hstable : (prefixWord ++ tailWord_1737965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1737965).length < 2 ^ (prefixWord ++ tailWord_1737965).sum := by decide
  have hdescent : baseEnd_1737965 < baseStart_1737965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1737965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738083 : List Nat := [1, 1, 1, 5, 2, 2, 1, 5, 3]
def baseStart_1738083 : Nat := 118140960795 + 1738083 * 2 ^ 59
def prefixEnd_1738083 : Nat := 4983230072969 + 3 ^ 40 * 1738083 * 2
def baseEnd_1738083 : Nat := 396654220626057100430759

theorem tailTrace_1738083 : CollatzResearch.WordTrace tailWord_1738083 prefixEnd_1738083 396654220626057100430759 := by
  unfold tailWord_1738083
  simp only [CollatzResearch.WordTrace]
  refine ⟨63393094962229606788794903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42262063308153071192529935 63393094962229606788794903)
  ·
    refine ⟨95089642443344410183192355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63393094962229606788794903 95089642443344410183192355)
    ·
      refine ⟨142634463665016615274788533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95089642443344410183192355 142634463665016615274788533)
      ·
        refine ⟨13371980968595307682011425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142634463665016615274788533 13371980968595307682011425)
        ·
          refine ⟨10028985726446480761508569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13371980968595307682011425 10028985726446480761508569)
          ·
            refine ⟨7521739294834860571131427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10028985726446480761508569 7521739294834860571131427)
            ·
              refine ⟨11282608942252290856697141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521739294834860571131427 11282608942252290856697141)
              ·
                refine ⟨1057744588336152267815357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11282608942252290856697141 1057744588336152267815357)
                ·
                  refine ⟨396654220626057100430759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057744588336152267815357 396654220626057100430759)
                  ·
                    rfl

theorem cell21_1738083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 3].length) (baseStart_1738083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738083 prefixEnd_1738083 := by exact prefixLift 1738083
  have htrace : WordTrace (prefixWord ++ tailWord_1738083) baseStart_1738083 baseEnd_1738083 := by
    simpa [prefixWord, tailWord_1738083, baseEnd_1738083] using wordTrace_append hprefix tailTrace_1738083
  have hstable : (prefixWord ++ tailWord_1738083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738083).length < 2 ^ (prefixWord ++ tailWord_1738083).sum := by decide
  have hdescent : baseEnd_1738083 < baseStart_1738083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738097 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 4]
def baseStart_1738097 : Nat := 118140960795 + 1738097 * 2 ^ 59
def prefixEnd_1738097 : Nat := 4983230072969 + 3 ^ 40 * 1738097 * 2
def baseEnd_1738097 : Nat := 396657415616796187197397

theorem tailTrace_1738097 : CollatzResearch.WordTrace tailWord_1738097 prefixEnd_1738097 396657415616796187197397 := by
  unfold tailWord_1738097
  simp only [CollatzResearch.WordTrace]
  refine ⟨63393605584178887179804545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42262403722785924786536363 63393605584178887179804545)
  ·
    refine ⟨47545204188134165384853409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63393605584178887179804545 47545204188134165384853409)
    ·
      refine ⟨35658903141100624038640057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47545204188134165384853409 35658903141100624038640057)
      ·
        refine ⟨26744177355825468028980043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35658903141100624038640057 26744177355825468028980043)
        ·
          refine ⟨40116266033738202043470065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26744177355825468028980043 40116266033738202043470065)
          ·
            refine ⟨30087199525303651532602549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40116266033738202043470065 30087199525303651532602549)
            ·
              refine ⟨2820674955497217331181489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30087199525303651532602549 2820674955497217331181489)
              ·
                refine ⟨2115506216622912998386117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2820674955497217331181489 2115506216622912998386117)
                ·
                  refine ⟨396657415616796187197397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2115506216622912998386117 396657415616796187197397)
                  ·
                    rfl

theorem cell21_1738097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_1738097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738097 prefixEnd_1738097 := by exact prefixLift 1738097
  have htrace : WordTrace (prefixWord ++ tailWord_1738097) baseStart_1738097 baseEnd_1738097 := by
    simpa [prefixWord, tailWord_1738097, baseEnd_1738097] using wordTrace_append hprefix tailTrace_1738097
  have hstable : (prefixWord ++ tailWord_1738097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738097).length < 2 ^ (prefixWord ++ tailWord_1738097).sum := by decide
  have hdescent : baseEnd_1738097 < baseStart_1738097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738156 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_1738156 : Nat := 118140960795 + 1738156 * 2 ^ 59
def prefixEnd_1738156 : Nat := 4983230072969 + 3 ^ 40 * 1738156 * 2
def baseEnd_1738156 : Nat := 396670880220625195713943

theorem tailTrace_1738156 : CollatzResearch.WordTrace tailWord_1738156 prefixEnd_1738156 396670880220625195713943 := by
  unfold tailWord_1738156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31697878745482570128101161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42263838327310093504134881 31697878745482570128101161)
  ·
    refine ⟨23773409059111927596075871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31697878745482570128101161 23773409059111927596075871)
    ·
      refine ⟨35660113588667891394113807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23773409059111927596075871 35660113588667891394113807)
      ·
        refine ⟨53490170383001837091170711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35660113588667891394113807 53490170383001837091170711)
        ·
          refine ⟨80235255574502755636756067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53490170383001837091170711 80235255574502755636756067)
          ·
            refine ⟨120352883361754133455134101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80235255574502755636756067 120352883361754133455134101)
            ·
              refine ⟨5641541407582225005709411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120352883361754133455134101 5641541407582225005709411)
              ·
                refine ⟨8462312111373337508564117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641541407582225005709411 8462312111373337508564117)
                ·
                  refine ⟨396670880220625195713943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8462312111373337508564117 396670880220625195713943)
                  ·
                    rfl

theorem cell21_1738156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_1738156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738156 prefixEnd_1738156 := by exact prefixLift 1738156
  have htrace : WordTrace (prefixWord ++ tailWord_1738156) baseStart_1738156 baseEnd_1738156 := by
    simpa [prefixWord, tailWord_1738156, baseEnd_1738156] using wordTrace_append hprefix tailTrace_1738156
  have hstable : (prefixWord ++ tailWord_1738156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738156).length < 2 ^ (prefixWord ++ tailWord_1738156).sum := by decide
  have hdescent : baseEnd_1738156 < baseStart_1738156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738173 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1738173 : Nat := 118140960795 + 1738173 * 2 ^ 59
def prefixEnd_1738173 : Nat := 4983230072969 + 3 ^ 40 * 1738173 * 2
def baseEnd_1738173 : Nat := 396674759852236943930575

theorem tailTrace_1738173 : CollatzResearch.WordTrace tailWord_1738173 prefixEnd_1738173 396674759852236943930575 := by
  unfold tailWord_1738173
  simp only [CollatzResearch.WordTrace]
  refine ⟨63396377531903552159571173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42264251687935701439714115 63396377531903552159571173)
  ·
    refine ⟨11886820787231916029919595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63396377531903552159571173 11886820787231916029919595)
    ·
      refine ⟨17830231180847874044879393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11886820787231916029919595 17830231180847874044879393)
      ·
        refine ⟨13372673385635905533659545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17830231180847874044879393 13372673385635905533659545)
        ·
          refine ⟨10029505039226929150244659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13372673385635905533659545 10029505039226929150244659)
          ·
            refine ⟨15044257558840393725366989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10029505039226929150244659 15044257558840393725366989)
            ·
              refine ⟨5641596584565147647012621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15044257558840393725366989 5641596584565147647012621)
              ·
                refine ⟨2115598719211930367629733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5641596584565147647012621 2115598719211930367629733)
                ·
                  refine ⟨396674759852236943930575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2115598719211930367629733 396674759852236943930575)
                  ·
                    rfl

theorem cell21_1738173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1738173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738173 prefixEnd_1738173 := by exact prefixLift 1738173
  have htrace : WordTrace (prefixWord ++ tailWord_1738173) baseStart_1738173 baseEnd_1738173 := by
    simpa [prefixWord, tailWord_1738173, baseEnd_1738173] using wordTrace_append hprefix tailTrace_1738173
  have hstable : (prefixWord ++ tailWord_1738173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738173).length < 2 ^ (prefixWord ++ tailWord_1738173).sum := by decide
  have hdescent : baseEnd_1738173 < baseStart_1738173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738221 : List Nat := [1, 5, 1, 3, 2, 2, 1, 6]
def baseStart_1738221 : Nat := 118140960795 + 1738221 * 2 ^ 59
def prefixEnd_1738221 : Nat := 4983230072969 + 3 ^ 40 * 1738221 * 2
def baseEnd_1738221 : Nat := 132228571368733175710159

theorem tailTrace_1738221 : CollatzResearch.WordTrace tailWord_1738221 prefixEnd_1738221 132228571368733175710159 := by
  unfold tailWord_1738221
  simp only [CollatzResearch.WordTrace]
  refine ⟨63398128235729656357318517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42265418823819770904879011 63398128235729656357318517)
  ·
    refine ⟨5943574522099655283498611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63398128235729656357318517 5943574522099655283498611)
    ·
      refine ⟨8915361783149482925247917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943574522099655283498611 8915361783149482925247917)
      ·
        refine ⟨3343260668681056096967969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8915361783149482925247917 3343260668681056096967969)
        ·
          refine ⟨2507445501510792072725977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3343260668681056096967969 2507445501510792072725977)
          ·
            refine ⟨1880584126133094054544483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2507445501510792072725977 1880584126133094054544483)
            ·
              refine ⟨2820876189199641081816725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880584126133094054544483 2820876189199641081816725)
              ·
                refine ⟨132228571368733175710159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2820876189199641081816725 132228571368733175710159)
                ·
                  rfl

theorem cell21_1738221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 6].length) (baseStart_1738221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738221 prefixEnd_1738221 := by exact prefixLift 1738221
  have htrace : WordTrace (prefixWord ++ tailWord_1738221) baseStart_1738221 baseEnd_1738221 := by
    simpa [prefixWord, tailWord_1738221, baseEnd_1738221] using wordTrace_append hprefix tailTrace_1738221
  have hstable : (prefixWord ++ tailWord_1738221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738221).length < 2 ^ (prefixWord ++ tailWord_1738221).sum := by decide
  have hdescent : baseEnd_1738221 < baseStart_1738221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738238 : List Nat := [4, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1738238 : Nat := 118140960795 + 1738238 * 2 ^ 59
def prefixEnd_1738238 : Nat := 4983230072969 + 3 ^ 40 * 1738238 * 2
def baseEnd_1738238 : Nat := 132229864579270425115703

theorem tailTrace_1738238 : CollatzResearch.WordTrace tailWord_1738238 prefixEnd_1738238 132229864579270425115703 := by
  unfold tailWord_1738238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924843534583508532585921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42265832184445378840458245 7924843534583508532585921)
  ·
    refine ⟨5943632650937631399439441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7924843534583508532585921 5943632650937631399439441)
    ·
      refine ⟨4457724488203223549579581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5943632650937631399439441 4457724488203223549579581)
      ·
        refine ⟨1671646683076208831092343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4457724488203223549579581 1671646683076208831092343)
        ·
          refine ⟨2507470024614313246638515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671646683076208831092343 2507470024614313246638515)
          ·
            refine ⟨3761205036921469869957773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507470024614313246638515 3761205036921469869957773)
            ·
              refine ⟨1410451888845551201234165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3761205036921469869957773 1410451888845551201234165)
              ·
                refine ⟨132229864579270425115703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1410451888845551201234165 132229864579270425115703)
                ·
                  rfl

theorem cell21_1738238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1738238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738238 prefixEnd_1738238 := by exact prefixLift 1738238
  have htrace : WordTrace (prefixWord ++ tailWord_1738238) baseStart_1738238 baseEnd_1738238 := by
    simpa [prefixWord, tailWord_1738238, baseEnd_1738238] using wordTrace_append hprefix tailTrace_1738238
  have hstable : (prefixWord ++ tailWord_1738238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738238).length < 2 ^ (prefixWord ++ tailWord_1738238).sum := by decide
  have hdescent : baseEnd_1738238 < baseStart_1738238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738252 : List Nat := [2, 2, 1, 2, 5, 1, 2, 3, 3]
def baseStart_1738252 : Nat := 118140960795 + 1738252 * 2 ^ 59
def prefixEnd_1738252 : Nat := 4983230072969 + 3 ^ 40 * 1738252 * 2
def baseEnd_1738252 : Nat := 396692788728550362113747

theorem tailTrace_1738252 : CollatzResearch.WordTrace tailWord_1738252 prefixEnd_1738252 396692788728550362113747 := by
  unfold tailWord_1738252
  simp only [CollatzResearch.WordTrace]
  refine ⟨31699629449308674325848505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42266172599078232434464673 31699629449308674325848505)
  ·
    refine ⟨23774722086981505744386379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31699629449308674325848505 23774722086981505744386379)
    ·
      refine ⟨35662083130472258616579569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23774722086981505744386379 35662083130472258616579569)
      ·
        refine ⟨26746562347854193962434677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35662083130472258616579569 26746562347854193962434677)
        ·
          refine ⟨2507490220111330683978251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26746562347854193962434677 2507490220111330683978251)
          ·
            refine ⟨3761235330166996025967377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507490220111330683978251 3761235330166996025967377)
            ·
              refine ⟨2820926497625247019475533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761235330166996025967377 2820926497625247019475533)
              ·
                refine ⟨1057847436609467632303325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2820926497625247019475533 1057847436609467632303325)
                ·
                  refine ⟨396692788728550362113747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057847436609467632303325 396692788728550362113747)
                  ·
                    rfl

theorem cell21_1738252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_1738252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738252 prefixEnd_1738252 := by exact prefixLift 1738252
  have htrace : WordTrace (prefixWord ++ tailWord_1738252) baseStart_1738252 baseEnd_1738252 := by
    simpa [prefixWord, tailWord_1738252, baseEnd_1738252] using wordTrace_append hprefix tailTrace_1738252
  have hstable : (prefixWord ++ tailWord_1738252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738252).length < 2 ^ (prefixWord ++ tailWord_1738252).sum := by decide
  have hdescent : baseEnd_1738252 < baseStart_1738252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738339 : List Nat := [1, 1, 1, 5, 1, 4, 2, 6]
def baseStart_1738339 : Nat := 118140960795 + 1738339 * 2 ^ 59
def prefixEnd_1738339 : Nat := 4983230072969 + 3 ^ 40 * 1738339 * 2
def baseEnd_1738339 : Nat := 132237547771285848054523

theorem tailTrace_1738339 : CollatzResearch.WordTrace tailWord_1738339 prefixEnd_1738339 132237547771285848054523 := by
  unfold tailWord_1738339
  simp only [CollatzResearch.WordTrace]
  refine ⟨63402432049302162510114071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42268288032868108340076047 63402432049302162510114071)
  ·
    refine ⟨95103648073953243765171107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63402432049302162510114071 95103648073953243765171107)
    ·
      refine ⟨142655472110929865647756661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95103648073953243765171107 142655472110929865647756661)
      ·
        refine ⟨13373950510399674904477187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142655472110929865647756661 13373950510399674904477187)
        ·
          refine ⟨20060925765599512356715781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13373950510399674904477187 20060925765599512356715781)
          ·
            refine ⟨3761423581049908566884209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20060925765599512356715781 3761423581049908566884209)
            ·
              refine ⟨2821067685787431425163157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761423581049908566884209 2821067685787431425163157)
              ·
                refine ⟨132237547771285848054523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2821067685787431425163157 132237547771285848054523)
                ·
                  rfl

theorem cell21_1738339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 6].length) (baseStart_1738339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738339 prefixEnd_1738339 := by exact prefixLift 1738339
  have htrace : WordTrace (prefixWord ++ tailWord_1738339) baseStart_1738339 baseEnd_1738339 := by
    simpa [prefixWord, tailWord_1738339, baseEnd_1738339] using wordTrace_append hprefix tailTrace_1738339
  have hstable : (prefixWord ++ tailWord_1738339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738339).length < 2 ^ (prefixWord ++ tailWord_1738339).sum := by decide
  have hdescent : baseEnd_1738339 < baseStart_1738339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738353 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 5]
def baseStart_1738353 : Nat := 118140960795 + 1738353 * 2 ^ 59
def prefixEnd_1738353 : Nat := 4983230072969 + 3 ^ 40 * 1738353 * 2
def baseEnd_1738353 : Nat := 396715838304596630930207

theorem tailTrace_1738353 : CollatzResearch.WordTrace tailWord_1738353 prefixEnd_1738353 396715838304596630930207 := by
  unfold tailWord_1738353
  simp only [CollatzResearch.WordTrace]
  refine ⟨63402942671251442901123713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42268628447500961934082475 63402942671251442901123713)
  ·
    refine ⟨47552207003438582175842785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63402942671251442901123713 47552207003438582175842785)
    ·
      refine ⟨35664155252578936631882089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47552207003438582175842785 35664155252578936631882089)
      ·
        refine ⟨26748116439434202473911567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35664155252578936631882089 26748116439434202473911567)
        ·
          refine ⟨40122174659151303710867351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26748116439434202473911567 40122174659151303710867351)
          ·
            refine ⟨60183261988726955566301027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40122174659151303710867351 60183261988726955566301027)
            ·
              refine ⟨90274892983090433349451541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60183261988726955566301027 90274892983090433349451541)
              ·
                refine ⟨4231635608582364063255541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90274892983090433349451541 4231635608582364063255541)
                ·
                  refine ⟨396715838304596630930207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4231635608582364063255541 396715838304596630930207)
                  ·
                    rfl

theorem cell21_1738353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_1738353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738353 prefixEnd_1738353 := by exact prefixLift 1738353
  have htrace : WordTrace (prefixWord ++ tailWord_1738353) baseStart_1738353 baseEnd_1738353 := by
    simpa [prefixWord, tailWord_1738353, baseEnd_1738353] using wordTrace_append hprefix tailTrace_1738353
  have hstable : (prefixWord ++ tailWord_1738353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738353).length < 2 ^ (prefixWord ++ tailWord_1738353).sum := by decide
  have hdescent : baseEnd_1738353 < baseStart_1738353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738401 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 4]
def baseStart_1738401 : Nat := 118140960795 + 1738401 * 2 ^ 59
def prefixEnd_1738401 : Nat := 4983230072969 + 3 ^ 40 * 1738401 * 2
def baseEnd_1738401 : Nat := 396726792558559214130109

theorem tailTrace_1738401 : CollatzResearch.WordTrace tailWord_1738401 prefixEnd_1738401 396726792558559214130109 := by
  unfold tailWord_1738401
  simp only [CollatzResearch.WordTrace]
  refine ⟨63404693375077547098871057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42269795583385031399247371 63404693375077547098871057)
  ·
    refine ⟨47553520031308160324153293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63404693375077547098871057 47553520031308160324153293)
    ·
      refine ⟨17832570011740560121557485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47553520031308160324153293 17832570011740560121557485)
      ·
        refine ⟨6687213754402710045584057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17832570011740560121557485 6687213754402710045584057)
        ·
          refine ⟨5015410315802032534188043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6687213754402710045584057 5015410315802032534188043)
          ·
            refine ⟨7523115473703048801282065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015410315802032534188043 7523115473703048801282065)
            ·
              refine ⟨5642336605277286600961549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7523115473703048801282065 5642336605277286600961549)
              ·
                refine ⟨2115876226978982475360581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5642336605277286600961549 2115876226978982475360581)
                ·
                  refine ⟨396726792558559214130109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2115876226978982475360581 396726792558559214130109)
                  ·
                    rfl

theorem cell21_1738401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_1738401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738401 prefixEnd_1738401 := by exact prefixLift 1738401
  have htrace : WordTrace (prefixWord ++ tailWord_1738401) baseStart_1738401 baseEnd_1738401 := by
    simpa [prefixWord, tailWord_1738401, baseEnd_1738401] using wordTrace_append hprefix tailTrace_1738401
  have hstable : (prefixWord ++ tailWord_1738401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738401).length < 2 ^ (prefixWord ++ tailWord_1738401).sum := by decide
  have hdescent : baseEnd_1738401 < baseStart_1738401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738415 : List Nat := [1, 1, 2, 1, 2, 4, 5, 5]
def baseStart_1738415 : Nat := 118140960795 + 1738415 * 2 ^ 59
def prefixEnd_1738415 : Nat := 4983230072969 + 3 ^ 40 * 1738415 * 2
def baseEnd_1738415 : Nat := 132243329183099433632249

theorem tailTrace_1738415 : CollatzResearch.WordTrace tailWord_1738415 prefixEnd_1738415 132243329183099433632249 := by
  unfold tailWord_1738415
  simp only [CollatzResearch.WordTrace]
  refine ⟨63405203997026827489880699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42270135998017884993253799 63405203997026827489880699)
  ·
    refine ⟨95107805995540241234821049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63405203997026827489880699 95107805995540241234821049)
    ·
      refine ⟨71330854496655180926115787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95107805995540241234821049 71330854496655180926115787)
      ·
        refine ⟨106996281744982771389173681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71330854496655180926115787 106996281744982771389173681)
        ·
          refine ⟨80247211308737078541880261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106996281744982771389173681 80247211308737078541880261)
          ·
            refine ⟨15046352120388202226602549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80247211308737078541880261 15046352120388202226602549)
            ·
              refine ⟨1410595511286393958743989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15046352120388202226602549 1410595511286393958743989)
              ·
                refine ⟨132243329183099433632249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1410595511286393958743989 132243329183099433632249)
                ·
                  rfl

theorem cell21_1738415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 5].length) (baseStart_1738415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738415 prefixEnd_1738415 := by exact prefixLift 1738415
  have htrace : WordTrace (prefixWord ++ tailWord_1738415) baseStart_1738415 baseEnd_1738415 := by
    simpa [prefixWord, tailWord_1738415, baseEnd_1738415] using wordTrace_append hprefix tailTrace_1738415
  have hstable : (prefixWord ++ tailWord_1738415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738415).length < 2 ^ (prefixWord ++ tailWord_1738415).sum := by decide
  have hdescent : baseEnd_1738415 < baseStart_1738415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738429 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 7]
def baseStart_1738429 : Nat := 118140960795 + 1738429 * 2 ^ 59
def prefixEnd_1738429 : Nat := 4983230072969 + 3 ^ 40 * 1738429 * 2
def baseEnd_1738429 : Nat := 396733182540037387663385

theorem tailTrace_1738429 : CollatzResearch.WordTrace tailWord_1738429 prefixEnd_1738429 396733182540037387663385 := by
  unfold tailWord_1738429
  simp only [CollatzResearch.WordTrace]
  refine ⟨63405714618976107880890341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42270476412650738587260227 63405714618976107880890341)
  ·
    refine ⟨11888571491058020227666939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63405714618976107880890341 11888571491058020227666939)
    ·
      refine ⟨17832857236587030341500409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11888571491058020227666939 17832857236587030341500409)
      ·
        refine ⟨13374642927440272756125307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17832857236587030341500409 13374642927440272756125307)
        ·
          refine ⟨20061964391160409134187961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13374642927440272756125307 20061964391160409134187961)
          ·
            refine ⟨15046473293370306850640971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20061964391160409134187961 15046473293370306850640971)
            ·
              refine ⟨22569709940055460275961457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15046473293370306850640971 22569709940055460275961457)
              ·
                refine ⟨16927282455041595206971093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22569709940055460275961457 16927282455041595206971093)
                ·
                  refine ⟨396733182540037387663385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16927282455041595206971093 396733182540037387663385)
                  ·
                    rfl

theorem cell21_1738429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_1738429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738429 prefixEnd_1738429 := by exact prefixLift 1738429
  have htrace : WordTrace (prefixWord ++ tailWord_1738429) baseStart_1738429 baseEnd_1738429 := by
    simpa [prefixWord, tailWord_1738429, baseEnd_1738429] using wordTrace_append hprefix tailTrace_1738429
  have hstable : (prefixWord ++ tailWord_1738429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738429).length < 2 ^ (prefixWord ++ tailWord_1738429).sum := by decide
  have hdescent : baseEnd_1738429 < baseStart_1738429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738446 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1738446 : Nat := 118140960795 + 1738446 * 2 ^ 59
def prefixEnd_1738446 : Nat := 4983230072969 + 3 ^ 40 * 1738446 * 2
def baseEnd_1738446 : Nat := 396737062171649135880017

theorem tailTrace_1738446 : CollatzResearch.WordTrace tailWord_1738446 prefixEnd_1738446 396737062171649135880017 := by
  unfold tailWord_1738446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7925791832489314973032399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42270889773276346522839461 7925791832489314973032399)
  ·
    refine ⟨11888687748733972459548599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7925791832489314973032399 11888687748733972459548599)
    ·
      refine ⟨17833031623100958689322899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11888687748733972459548599 17833031623100958689322899)
      ·
        refine ⟨26749547434651438033984349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17833031623100958689322899 26749547434651438033984349)
        ·
          refine ⟨10031080287994289262744131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26749547434651438033984349 10031080287994289262744131)
          ·
            refine ⟨15046620431991433894116197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10031080287994289262744131 15046620431991433894116197)
            ·
              refine ⟨2821241330998393855146787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15046620431991433894116197 2821241330998393855146787)
              ·
                refine ⟨4231861996497590782720181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821241330998393855146787 4231861996497590782720181)
                ·
                  refine ⟨396737062171649135880017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4231861996497590782720181 396737062171649135880017)
                  ·
                    rfl

theorem cell21_1738446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1738446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738446 prefixEnd_1738446 := by exact prefixLift 1738446
  have htrace : WordTrace (prefixWord ++ tailWord_1738446) baseStart_1738446 baseEnd_1738446 := by
    simpa [prefixWord, tailWord_1738446, baseEnd_1738446] using wordTrace_append hprefix tailTrace_1738446
  have hstable : (prefixWord ++ tailWord_1738446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738446).length < 2 ^ (prefixWord ++ tailWord_1738446).sum := by decide
  have hdescent : baseEnd_1738446 < baseStart_1738446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738581 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 7]
def baseStart_1738581 : Nat := 118140960795 + 1738581 * 2 ^ 59
def prefixEnd_1738581 : Nat := 4983230072969 + 3 ^ 40 * 1738581 * 2
def baseEnd_1738581 : Nat := 396767871010918901129741

theorem tailTrace_1738581 : CollatzResearch.WordTrace tailWord_1738581 prefixEnd_1738581 396767871010918901129741 := by
  unfold tailWord_1738581
  simp only [CollatzResearch.WordTrace]
  refine ⟨63411258514425437840423597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42274172342950291893615731 63411258514425437840423597)
  ·
    refine ⟨23779221942909539190158849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63411258514425437840423597 23779221942909539190158849)
    ·
      refine ⟨17834416457182154392619137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23779221942909539190158849 17834416457182154392619137)
      ·
        refine ⟨13375812342886615794464353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17834416457182154392619137 13375812342886615794464353)
        ·
          refine ⟨10031859257164961845848265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13375812342886615794464353 10031859257164961845848265)
          ·
            refine ⟨7523894442873721384386199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10031859257164961845848265 7523894442873721384386199)
            ·
              refine ⟨11285841664310582076579299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7523894442873721384386199 11285841664310582076579299)
              ·
                refine ⟨16928762496465873114868949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11285841664310582076579299 16928762496465873114868949)
                ·
                  refine ⟨396767871010918901129741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16928762496465873114868949 396767871010918901129741)
                  ·
                    rfl

theorem cell21_1738581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_1738581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738581 prefixEnd_1738581 := by exact prefixLift 1738581
  have htrace : WordTrace (prefixWord ++ tailWord_1738581) baseStart_1738581 baseEnd_1738581 := by
    simpa [prefixWord, tailWord_1738581, baseEnd_1738581] using wordTrace_append hprefix tailTrace_1738581
  have hstable : (prefixWord ++ tailWord_1738581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738581).length < 2 ^ (prefixWord ++ tailWord_1738581).sum := by decide
  have hdescent : baseEnd_1738581 < baseStart_1738581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738629 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 4]
def baseStart_1738629 : Nat := 118140960795 + 1738629 * 2 ^ 59
def prefixEnd_1738629 : Nat := 4983230072969 + 3 ^ 40 * 1738629 * 2
def baseEnd_1738629 : Nat := 396778825264881484329643

theorem tailTrace_1738629 : CollatzResearch.WordTrace tailWord_1738629 prefixEnd_1738629 396778825264881484329643 := by
  unfold tailWord_1738629
  simp only [CollatzResearch.WordTrace]
  refine ⟨63413009218251542038170941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42275339478834361358780627 63413009218251542038170941)
  ·
    refine ⟨23779878456844328264314103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63413009218251542038170941 23779878456844328264314103)
    ·
      refine ⟨35669817685266492396471155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23779878456844328264314103 35669817685266492396471155)
      ·
        refine ⟨53504726527899738594706733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35669817685266492396471155 53504726527899738594706733)
        ·
          refine ⟨20064272447962401973015025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53504726527899738594706733 20064272447962401973015025)
          ·
            refine ⟨15048204335971801479761269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20064272447962401973015025 15048204335971801479761269)
            ·
              refine ⟨1410769156497356388727619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15048204335971801479761269 1410769156497356388727619)
              ·
                refine ⟨2116153734746034583091429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410769156497356388727619 2116153734746034583091429)
                ·
                  refine ⟨396778825264881484329643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116153734746034583091429 396778825264881484329643)
                  ·
                    rfl

theorem cell21_1738629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_1738629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738629 prefixEnd_1738629 := by exact prefixLift 1738629
  have htrace : WordTrace (prefixWord ++ tailWord_1738629) baseStart_1738629 baseEnd_1738629 := by
    simpa [prefixWord, tailWord_1738629, baseEnd_1738629] using wordTrace_append hprefix tailTrace_1738629
  have hstable : (prefixWord ++ tailWord_1738629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738629).length < 2 ^ (prefixWord ++ tailWord_1738629).sum := by decide
  have hdescent : baseEnd_1738629 < baseStart_1738629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738671 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 6]
def baseStart_1738671 : Nat := 118140960795 + 1738671 * 2 ^ 59
def prefixEnd_1738671 : Nat := 4983230072969 + 3 ^ 40 * 1738671 * 2
def baseEnd_1738671 : Nat := 396788410237098744629557

theorem tailTrace_1738671 : CollatzResearch.WordTrace tailWord_1738671 prefixEnd_1738671 396788410237098744629557 := by
  unfold tailWord_1738671
  simp only [CollatzResearch.WordTrace]
  refine ⟨63414541084099383211199867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42276360722732922140799911 63414541084099383211199867)
  ·
    refine ⟨95121811626149074816799801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63414541084099383211199867 95121811626149074816799801)
    ·
      refine ⟨71341358719611806112599851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95121811626149074816799801 71341358719611806112599851)
      ·
        refine ⟨107012038079417709168899777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71341358719611806112599851 107012038079417709168899777)
        ·
          refine ⟨80259028559563281876674833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107012038079417709168899777 80259028559563281876674833)
          ·
            refine ⟨60194271419672461407506125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80259028559563281876674833 60194271419672461407506125)
            ·
              refine ⟨22572851782377173027814797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60194271419672461407506125 22572851782377173027814797)
              ·
                refine ⟨8464819418391439885430549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22572851782377173027814797 8464819418391439885430549)
                ·
                  refine ⟨396788410237098744629557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8464819418391439885430549 396788410237098744629557)
                  ·
                    rfl

theorem cell21_1738671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_1738671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738671 prefixEnd_1738671 := by exact prefixLift 1738671
  have htrace : WordTrace (prefixWord ++ tailWord_1738671) baseStart_1738671 baseEnd_1738671 := by
    simpa [prefixWord, tailWord_1738671, baseEnd_1738671] using wordTrace_append hprefix tailTrace_1738671
  have hstable : (prefixWord ++ tailWord_1738671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738671).length < 2 ^ (prefixWord ++ tailWord_1738671).sum := by decide
  have hdescent : baseEnd_1738671 < baseStart_1738671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738674 : List Nat := [3, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_1738674 : Nat := 118140960795 + 1738674 * 2 ^ 59
def prefixEnd_1738674 : Nat := 4983230072969 + 3 ^ 40 * 1738674 * 2
def baseEnd_1738674 : Nat := 396789094877971406079551

theorem tailTrace_1738674 : CollatzResearch.WordTrace tailWord_1738674 prefixEnd_1738674 396789094877971406079551 := by
  unfold tailWord_1738674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15853662625772128680889769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42276433668725676482372717 15853662625772128680889769)
  ·
    refine ⟨11890246969329096510667327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15853662625772128680889769 11890246969329096510667327)
    ·
      refine ⟨17835370453993644766000991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11890246969329096510667327 17835370453993644766000991)
      ·
        refine ⟨26753055680990467149001487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17835370453993644766000991 26753055680990467149001487)
        ·
          refine ⟨40129583521485700723502231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26753055680990467149001487 40129583521485700723502231)
          ·
            refine ⟨60194375282228551085253347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40129583521485700723502231 60194375282228551085253347)
            ·
              refine ⟨90291562923342826627880021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60194375282228551085253347 90291562923342826627880021)
              ·
                refine ⟨1058104253007923749545469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 90291562923342826627880021 1058104253007923749545469)
                ·
                  refine ⟨396789094877971406079551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058104253007923749545469 396789094877971406079551)
                  ·
                    rfl

theorem cell21_1738674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_1738674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738674 prefixEnd_1738674 := by exact prefixLift 1738674
  have htrace : WordTrace (prefixWord ++ tailWord_1738674) baseStart_1738674 baseEnd_1738674 := by
    simpa [prefixWord, tailWord_1738674, baseEnd_1738674] using wordTrace_append hprefix tailTrace_1738674
  have hstable : (prefixWord ++ tailWord_1738674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738674).length < 2 ^ (prefixWord ++ tailWord_1738674).sum := by decide
  have hdescent : baseEnd_1738674 < baseStart_1738674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738688 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_1738688 : Nat := 118140960795 + 1738688 * 2 ^ 59
def prefixEnd_1738688 : Nat := 4983230072969 + 3 ^ 40 * 1738688 * 2
def baseEnd_1738688 : Nat := 396792289868710492846189

theorem tailTrace_1738688 : CollatzResearch.WordTrace tailWord_1738688 prefixEnd_1738688 396792289868710492846189 := by
  unfold tailWord_1738688
  simp only [CollatzResearch.WordTrace]
  refine ⟨31707580562518897557284359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42276774083358530076379145 31707580562518897557284359)
  ·
    refine ⟨47561370843778346335926539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31707580562518897557284359 47561370843778346335926539)
    ·
      refine ⟨71342056265667519503889809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47561370843778346335926539 71342056265667519503889809)
      ·
        refine ⟨53506542199250639627917357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71342056265667519503889809 53506542199250639627917357)
        ·
          refine ⟨20064953324718989860469009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53506542199250639627917357 20064953324718989860469009)
          ·
            refine ⟨15048714993539242395351757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20064953324718989860469009 15048714993539242395351757)
            ·
              refine ⟨5643268122577215898256909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15048714993539242395351757 5643268122577215898256909)
              ·
                refine ⟨2116225545966455961846341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5643268122577215898256909 2116225545966455961846341)
                ·
                  refine ⟨396792289868710492846189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116225545966455961846341 396792289868710492846189)
                  ·
                    rfl

theorem cell21_1738688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_1738688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738688 prefixEnd_1738688 := by exact prefixLift 1738688
  have htrace : WordTrace (prefixWord ++ tailWord_1738688) baseStart_1738688 baseEnd_1738688 := by
    simpa [prefixWord, tailWord_1738688, baseEnd_1738688] using wordTrace_append hprefix tailTrace_1738688
  have hstable : (prefixWord ++ tailWord_1738688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738688).length < 2 ^ (prefixWord ++ tailWord_1738688).sum := by decide
  have hdescent : baseEnd_1738688 < baseStart_1738688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738702 : List Nat := [4, 1, 1, 1, 2, 2, 1, 9]
def baseStart_1738702 : Nat := 118140960795 + 1738702 * 2 ^ 59
def prefixEnd_1738702 : Nat := 4983230072969 + 3 ^ 40 * 1738702 * 2
def baseEnd_1738702 : Nat := 132265161619816526537609

theorem tailTrace_1738702 : CollatzResearch.WordTrace tailWord_1738702 prefixEnd_1738702 132265161619816526537609 := by
  unfold tailWord_1738702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926958968373384438197295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42277114497991383670385573 7926958968373384438197295)
  ·
    refine ⟨11890438452560076657295943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7926958968373384438197295 11890438452560076657295943)
    ·
      refine ⟨17835657678840114985943915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11890438452560076657295943 17835657678840114985943915)
      ·
        refine ⟨26753486518260172478915873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17835657678840114985943915 26753486518260172478915873)
        ·
          refine ⟨20065114888695129359186905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26753486518260172478915873 20065114888695129359186905)
          ·
            refine ⟨15048836166521347019390179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20065114888695129359186905 15048836166521347019390179)
            ·
              refine ⟨22573254249782020529085269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15048836166521347019390179 22573254249782020529085269)
              ·
                refine ⟨132265161619816526537609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22573254249782020529085269 132265161619816526537609)
                ·
                  rfl

theorem cell21_1738702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_1738702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738702 prefixEnd_1738702 := by exact prefixLift 1738702
  have htrace : WordTrace (prefixWord ++ tailWord_1738702) baseStart_1738702 baseEnd_1738702 := by
    simpa [prefixWord, tailWord_1738702, baseEnd_1738702] using wordTrace_append hprefix tailTrace_1738702
  have hstable : (prefixWord ++ tailWord_1738702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738702).length < 2 ^ (prefixWord ++ tailWord_1738702).sum := by decide
  have hdescent : baseEnd_1738702 < baseStart_1738702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738750 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1738750 : Nat := 118140960795 + 1738750 * 2 ^ 59
def prefixEnd_1738750 : Nat := 4983230072969 + 3 ^ 40 * 1738750 * 2
def baseEnd_1738750 : Nat := 396806439113412162812729

theorem tailTrace_1738750 : CollatzResearch.WordTrace tailWord_1738750 prefixEnd_1738750 396806439113412162812729 := by
  unfold tailWord_1738750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927177806351647462915713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42278281633875453135550469 7927177806351647462915713)
  ·
    refine ⟨5945383354763735597186785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7927177806351647462915713 5945383354763735597186785)
    ·
      refine ⟨4459037516072801697890089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5945383354763735597186785 4459037516072801697890089)
      ·
        refine ⟨3344278137054601273417567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4459037516072801697890089 3344278137054601273417567)
        ·
          refine ⟨5016417205581901910126351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344278137054601273417567 5016417205581901910126351)
          ·
            refine ⟨7524625808372852865189527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016417205581901910126351 7524625808372852865189527)
            ·
              refine ⟨11286938712559279297784291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524625808372852865189527 11286938712559279297784291)
              ·
                refine ⟨16930408068838918946676437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11286938712559279297784291 16930408068838918946676437)
                ·
                  refine ⟨396806439113412162812729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16930408068838918946676437 396806439113412162812729)
                  ·
                    rfl

theorem cell21_1738750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1738750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738750 prefixEnd_1738750 := by exact prefixLift 1738750
  have htrace : WordTrace (prefixWord ++ tailWord_1738750) baseStart_1738750 baseEnd_1738750 := by
    simpa [prefixWord, tailWord_1738750, baseEnd_1738750] using wordTrace_append hprefix tailTrace_1738750
  have hstable : (prefixWord ++ tailWord_1738750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738750).length < 2 ^ (prefixWord ++ tailWord_1738750).sum := by decide
  have hdescent : baseEnd_1738750 < baseStart_1738750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738778 : List Nat := [3, 1, 1, 3, 1, 4, 8]
def baseStart_1738778 : Nat := 118140960795 + 1738778 * 2 ^ 59
def prefixEnd_1738778 : Nat := 4983230072969 + 3 ^ 40 * 1738778 * 2
def baseEnd_1738778 : Nat := 44090314343876704038445

theorem tailTrace_1738778 : CollatzResearch.WordTrace tailWord_1738778 prefixEnd_1738778 44090314343876704038445 := by
  unfold tailWord_1738778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15854610923677935121336247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42278962463141160323563325 15854610923677935121336247)
  ·
    refine ⟨23781916385516902682004371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15854610923677935121336247 23781916385516902682004371)
    ·
      refine ⟨35672874578275354023006557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23781916385516902682004371 35672874578275354023006557)
      ·
        refine ⟨13377327966853257758627459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35672874578275354023006557 13377327966853257758627459)
        ·
          refine ⟨20065991950279886637941189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13377327966853257758627459 20065991950279886637941189)
          ·
            refine ⟨3762373490677478744613973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20065991950279886637941189 3762373490677478744613973)
            ·
              refine ⟨44090314343876704038445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3762373490677478744613973 44090314343876704038445)
              ·
                rfl

theorem cell21_1738778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 8].length) (baseStart_1738778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738778 prefixEnd_1738778 := by exact prefixLift 1738778
  have htrace : WordTrace (prefixWord ++ tailWord_1738778) baseStart_1738778 baseEnd_1738778 := by
    simpa [prefixWord, tailWord_1738778, baseEnd_1738778] using wordTrace_append hprefix tailTrace_1738778
  have hstable : (prefixWord ++ tailWord_1738778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738778).length < 2 ^ (prefixWord ++ tailWord_1738778).sum := by decide
  have hdescent : baseEnd_1738778 < baseStart_1738778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738781 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 4]
def baseStart_1738781 : Nat := 118140960795 + 1738781 * 2 ^ 59
def prefixEnd_1738781 : Nat := 4983230072969 + 3 ^ 40 * 1738781 * 2
def baseEnd_1738781 : Nat := 396813513735762997795999

theorem tailTrace_1738781 : CollatzResearch.WordTrace tailWord_1738781 prefixEnd_1738781 396813513735762997795999 := by
  unfold tailWord_1738781
  simp only [CollatzResearch.WordTrace]
  refine ⟨63418553113700871997704197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42279035409133914665136131 63418553113700871997704197)
  ·
    refine ⟨11890978708818913499569537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63418553113700871997704197 11890978708818913499569537)
    ·
      refine ⟨8918234031614185124677153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11890978708818913499569537 8918234031614185124677153)
      ·
        refine ⟨6688675523710638843507865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8918234031614185124677153 6688675523710638843507865)
        ·
          refine ⟨5016506642782979132630899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6688675523710638843507865 5016506642782979132630899)
          ·
            refine ⟨7524759964174468698946349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016506642782979132630899 7524759964174468698946349)
            ·
              refine ⟨2821784986565425762104881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7524759964174468698946349 2821784986565425762104881)
              ·
                refine ⟨2116338739924069321578661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821784986565425762104881 2116338739924069321578661)
                ·
                  refine ⟨396813513735762997795999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116338739924069321578661 396813513735762997795999)
                  ·
                    rfl

theorem cell21_1738781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_1738781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738781 prefixEnd_1738781 := by exact prefixLift 1738781
  have htrace : WordTrace (prefixWord ++ tailWord_1738781) baseStart_1738781 baseEnd_1738781 := by
    simpa [prefixWord, tailWord_1738781, baseEnd_1738781] using wordTrace_append hprefix tailTrace_1738781
  have hstable : (prefixWord ++ tailWord_1738781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738781).length < 2 ^ (prefixWord ++ tailWord_1738781).sum := by decide
  have hdescent : baseEnd_1738781 < baseStart_1738781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738798 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1738798 : Nat := 118140960795 + 1738798 * 2 ^ 59
def prefixEnd_1738798 : Nat := 4983230072969 + 3 ^ 40 * 1738798 * 2
def baseEnd_1738798 : Nat := 396817393367374746012631

theorem tailTrace_1738798 : CollatzResearch.WordTrace tailWord_1738798 prefixEnd_1738798 396817393367374746012631 := by
  unfold tailWord_1738798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927396644329910487634131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42279448769759522600715365 7927396644329910487634131)
  ·
    refine ⟨11891094966494865731451197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7927396644329910487634131 11891094966494865731451197)
    ·
      refine ⟨4459160612435574649294199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11891094966494865731451197 4459160612435574649294199)
      ·
        refine ⟨6688740918653361973941299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4459160612435574649294199 6688740918653361973941299)
        ·
          refine ⟨10033111377980042960911949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6688740918653361973941299 10033111377980042960911949)
          ·
            refine ⟨3762416766742516110341981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10033111377980042960911949 3762416766742516110341981)
            ·
              refine ⟨1410906287528443541378243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3762416766742516110341981 1410906287528443541378243)
              ·
                refine ⟨2116359431292665312067365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410906287528443541378243 2116359431292665312067365)
                ·
                  refine ⟨396817393367374746012631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116359431292665312067365 396817393367374746012631)
                  ·
                    rfl

theorem cell21_1738798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1738798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738798 prefixEnd_1738798 := by exact prefixLift 1738798
  have htrace : WordTrace (prefixWord ++ tailWord_1738798) baseStart_1738798 baseEnd_1738798 := by
    simpa [prefixWord, tailWord_1738798, baseEnd_1738798] using wordTrace_append hprefix tailTrace_1738798
  have hstable : (prefixWord ++ tailWord_1738798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738798).length < 2 ^ (prefixWord ++ tailWord_1738798).sum := by decide
  have hdescent : baseEnd_1738798 < baseStart_1738798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1738823 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 8]
def baseStart_1738823 : Nat := 118140960795 + 1738823 * 2 ^ 59
def prefixEnd_1738823 : Nat := 4983230072969 + 3 ^ 40 * 1738823 * 2
def baseEnd_1738823 : Nat := 396823098707980258095913

theorem tailTrace_1738823 : CollatzResearch.WordTrace tailWord_1738823 prefixEnd_1738823 396823098707980258095913 := by
  unfold tailWord_1738823
  simp only [CollatzResearch.WordTrace]
  refine ⟨63420084979548713170733123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42280056653032475447155415 63420084979548713170733123)
  ·
    refine ⟨95130127469323069756099685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63420084979548713170733123 95130127469323069756099685)
    ·
      refine ⟨17836898900498075579268691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95130127469323069756099685 17836898900498075579268691)
      ·
        refine ⟨26755348350747113368903037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17836898900498075579268691 26755348350747113368903037)
        ·
          refine ⟨10033255631530167513338639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26755348350747113368903037 10033255631530167513338639)
          ·
            refine ⟨15049883447295251270007959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033255631530167513338639 15049883447295251270007959)
            ·
              refine ⟨22574825170942876905011939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049883447295251270007959 22574825170942876905011939)
              ·
                refine ⟨33862237756414315357517909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22574825170942876905011939 33862237756414315357517909)
                ·
                  refine ⟨396823098707980258095913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33862237756414315357517909 396823098707980258095913)
                  ·
                    rfl

theorem cell21_1738823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_1738823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1738823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1738823 prefixEnd_1738823 := by exact prefixLift 1738823
  have htrace : WordTrace (prefixWord ++ tailWord_1738823) baseStart_1738823 baseEnd_1738823 := by
    simpa [prefixWord, tailWord_1738823, baseEnd_1738823] using wordTrace_append hprefix tailTrace_1738823
  have hstable : (prefixWord ++ tailWord_1738823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1738823).length < 2 ^ (prefixWord ++ tailWord_1738823).sum := by decide
  have hdescent : baseEnd_1738823 < baseStart_1738823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1738823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739012 : List Nat := [2, 3, 2, 2, 3, 1, 3, 2, 3]
def baseStart_1739012 : Nat := 118140960795 + 1739012 * 2 ^ 59
def prefixEnd_1739012 : Nat := 4983230072969 + 3 ^ 40 * 1739012 * 2
def baseEnd_1739012 : Nat := 396866231082957929445527

theorem tailTrace_1739012 : CollatzResearch.WordTrace tailWord_1739012 prefixEnd_1739012 396866231082957929445527 := by
  unfold tailWord_1739012
  simp only [CollatzResearch.WordTrace]
  refine ⟨31713489187931999224681645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42284652250575998966242193 31713489187931999224681645)
  ·
    refine ⟨11892558445474499709255617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31713489187931999224681645 11892558445474499709255617)
    ·
      refine ⟨8919418834105874781941713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11892558445474499709255617 8919418834105874781941713)
      ·
        refine ⟨6689564125579406086456285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8919418834105874781941713 6689564125579406086456285)
        ·
          refine ⟨2508586547092277282421107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6689564125579406086456285 2508586547092277282421107)
          ·
            refine ⟨3762879820638415923631661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508586547092277282421107 3762879820638415923631661)
            ·
              refine ⟨1411079932739405971361873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3762879820638415923631661 1411079932739405971361873)
              ·
                refine ⟨1058309949554554478521405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411079932739405971361873 1058309949554554478521405)
                ·
                  refine ⟨396866231082957929445527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058309949554554478521405 396866231082957929445527)
                  ·
                    rfl

theorem cell21_1739012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_1739012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739012 prefixEnd_1739012 := by exact prefixLift 1739012
  have htrace : WordTrace (prefixWord ++ tailWord_1739012) baseStart_1739012 baseEnd_1739012 := by
    simpa [prefixWord, tailWord_1739012, baseEnd_1739012] using wordTrace_append hprefix tailTrace_1739012
  have hstable : (prefixWord ++ tailWord_1739012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739012).length < 2 ^ (prefixWord ++ tailWord_1739012).sum := by decide
  have hdescent : baseEnd_1739012 < baseStart_1739012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739068 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_1739068 : Nat := 118140960795 + 1739068 * 2 ^ 59
def prefixEnd_1739068 : Nat := 4983230072969 + 3 ^ 40 * 1739068 * 2
def baseEnd_1739068 : Nat := 396879011045914276512079

theorem tailTrace_1739068 : CollatzResearch.WordTrace tailWord_1739068 prefixEnd_1739068 396879011045914276512079 := by
  unfold tailWord_1739068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31714510431830560006700929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42286013909107413342267905 31714510431830560006700929)
  ·
    refine ⟨23785882823872920005025697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31714510431830560006700929 23785882823872920005025697)
    ·
      refine ⟨17839412117904690003769273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23785882823872920005025697 17839412117904690003769273)
      ·
        refine ⟨13379559088428517502826955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17839412117904690003769273 13379559088428517502826955)
        ·
          refine ⟨20069338632642776254240433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13379559088428517502826955 20069338632642776254240433)
          ·
            refine ⟨15052003974482082190680325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20069338632642776254240433 15052003974482082190680325)
            ·
              refine ⟨2822250745215390410752561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15052003974482082190680325 2822250745215390410752561)
              ·
                refine ⟨2116688058911542808064421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822250745215390410752561 2116688058911542808064421)
                ·
                  refine ⟨396879011045914276512079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116688058911542808064421 396879011045914276512079)
                  ·
                    rfl

theorem cell21_1739068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_1739068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739068 prefixEnd_1739068 := by exact prefixLift 1739068
  have htrace : WordTrace (prefixWord ++ tailWord_1739068) baseStart_1739068 baseEnd_1739068 := by
    simpa [prefixWord, tailWord_1739068, baseEnd_1739068] using wordTrace_append hprefix tailTrace_1739068
  have hstable : (prefixWord ++ tailWord_1739068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739068).length < 2 ^ (prefixWord ++ tailWord_1739068).sum := by decide
  have hdescent : baseEnd_1739068 < baseStart_1739068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739127 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 4]
def baseStart_1739127 : Nat := 118140960795 + 1739127 * 2 ^ 59
def prefixEnd_1739127 : Nat := 4983230072969 + 3 ^ 40 * 1739127 * 2
def baseEnd_1739127 : Nat := 396892475649743285028625

theorem tailTrace_1739127 : CollatzResearch.WordTrace tailWord_1739127 prefixEnd_1739127 396892475649743285028625 := by
  unfold tailWord_1739127
  simp only [CollatzResearch.WordTrace]
  refine ⟨63431172770447373089799635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42287448513631582059866423 63431172770447373089799635)
  ·
    refine ⟨95146759155671059634699453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63431172770447373089799635 95146759155671059634699453)
    ·
      refine ⟨35680034683376647363012295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95146759155671059634699453 35680034683376647363012295)
      ·
        refine ⟨53520052025064971044518443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35680034683376647363012295 53520052025064971044518443)
        ·
          refine ⟨80280078037597456566777665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53520052025064971044518443 80280078037597456566777665)
          ·
            refine ⟨60210058528198092425083249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80280078037597456566777665 60210058528198092425083249)
            ·
              refine ⟨45157543896148569318812437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60210058528198092425083249 45157543896148569318812437)
              ·
                refine ⟨2116759870131964186819333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45157543896148569318812437 2116759870131964186819333)
                ·
                  refine ⟨396892475649743285028625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116759870131964186819333 396892475649743285028625)
                  ·
                    rfl

theorem cell21_1739127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 4].length) (baseStart_1739127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739127 prefixEnd_1739127 := by exact prefixLift 1739127
  have htrace : WordTrace (prefixWord ++ tailWord_1739127) baseStart_1739127 baseEnd_1739127 := by
    simpa [prefixWord, tailWord_1739127, baseEnd_1739127] using wordTrace_append hprefix tailTrace_1739127
  have hstable : (prefixWord ++ tailWord_1739127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739127).length < 2 ^ (prefixWord ++ tailWord_1739127).sum := by decide
  have hdescent : baseEnd_1739127 < baseStart_1739127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739141 : List Nat := [1, 3, 1, 1, 3, 1, 1, 10]
def baseStart_1739141 : Nat := 118140960795 + 1739141 * 2 ^ 59
def prefixEnd_1739141 : Nat := 4983230072969 + 3 ^ 40 * 1739141 * 2
def baseEnd_1739141 : Nat := 132298556880160790598421

theorem tailTrace_1739141 : CollatzResearch.WordTrace tailWord_1739141 prefixEnd_1739141 132298556880160790598421 := by
  unfold tailWord_1739141
  simp only [CollatzResearch.WordTrace]
  refine ⟨63431683392396653480809277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42287788928264435653872851 63431683392396653480809277)
  ·
    refine ⟨23786881272148745055303479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63431683392396653480809277 23786881272148745055303479)
    ·
      refine ⟨35680321908223117582955219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23786881272148745055303479 35680321908223117582955219)
      ·
        refine ⟨53520482862334676374432829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35680321908223117582955219 53520482862334676374432829)
        ·
          refine ⟨20070181073375503640412311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53520482862334676374432829 20070181073375503640412311)
          ·
            refine ⟨30105271610063255460618467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20070181073375503640412311 30105271610063255460618467)
            ·
              refine ⟨45157907415094883190927701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30105271610063255460618467 45157907415094883190927701)
              ·
                refine ⟨132298556880160790598421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45157907415094883190927701 132298556880160790598421)
                ·
                  rfl

theorem cell21_1739141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 10].length) (baseStart_1739141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739141 prefixEnd_1739141 := by exact prefixLift 1739141
  have htrace : WordTrace (prefixWord ++ tailWord_1739141) baseStart_1739141 baseEnd_1739141 := by
    simpa [prefixWord, tailWord_1739141, baseEnd_1739141] using wordTrace_append hprefix tailTrace_1739141
  have hstable : (prefixWord ++ tailWord_1739141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739141).length < 2 ^ (prefixWord ++ tailWord_1739141).sum := by decide
  have hdescent : baseEnd_1739141 < baseStart_1739141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739172 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1739172 : Nat := 118140960795 + 1739172 * 2 ^ 59
def prefixEnd_1739172 : Nat := 4983230072969 + 3 ^ 40 * 1739172 * 2
def baseEnd_1739172 : Nat := 396902745262833206778533

theorem tailTrace_1739172 : CollatzResearch.WordTrace tailWord_1739172 prefixEnd_1739172 396902745262833206778533 := by
  unfold tailWord_1739172
  simp only [CollatzResearch.WordTrace]
  refine ⟨31716407027642172887593885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42288542703522897183458513 31716407027642172887593885)
  ·
    refine ⟨11893652635365814832847707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31716407027642172887593885 11893652635365814832847707)
    ·
      refine ⟨17840478953048722249271561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11893652635365814832847707 17840478953048722249271561)
      ·
        refine ⟨13380359214786541686953671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17840478953048722249271561 13380359214786541686953671)
        ·
          refine ⟨20070538822179812530430507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13380359214786541686953671 20070538822179812530430507)
          ·
            refine ⟨30105808233269718795645761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20070538822179812530430507 30105808233269718795645761)
            ·
              refine ⟨22579356174952289096734321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30105808233269718795645761 22579356174952289096734321)
              ·
                refine ⟨16934517131214216822550741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22579356174952289096734321 16934517131214216822550741)
                ·
                  refine ⟨396902745262833206778533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16934517131214216822550741 396902745262833206778533)
                  ·
                    rfl

theorem cell21_1739172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1739172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739172 prefixEnd_1739172 := by exact prefixLift 1739172
  have htrace : WordTrace (prefixWord ++ tailWord_1739172) baseStart_1739172 baseEnd_1739172 := by
    simpa [prefixWord, tailWord_1739172, baseEnd_1739172] using wordTrace_append hprefix tailTrace_1739172
  have hstable : (prefixWord ++ tailWord_1739172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739172).length < 2 ^ (prefixWord ++ tailWord_1739172).sum := by decide
  have hdescent : baseEnd_1739172 < baseStart_1739172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739237 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 4]
def baseStart_1739237 : Nat := 118140960795 + 1739237 * 2 ^ 59
def prefixEnd_1739237 : Nat := 4983230072969 + 3 ^ 40 * 1739237 * 2
def baseEnd_1739237 : Nat := 396917579148407538195067

theorem tailTrace_1739237 : CollatzResearch.WordTrace tailWord_1739237 prefixEnd_1739237 396917579148407538195067 := by
  unfold tailWord_1739237
  simp only [CollatzResearch.WordTrace]
  refine ⟨63435184800048861876303965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42290123200032574584202643 63435184800048861876303965)
  ·
    refine ⟨23788194300018323203613987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63435184800048861876303965 23788194300018323203613987)
    ·
      refine ⟨35682291450027484805420981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23788194300018323203613987 35682291450027484805420981)
      ·
        refine ⟨3345214823440076700508217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35682291450027484805420981 3345214823440076700508217)
        ·
          refine ⟨2508911117580057525381163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3345214823440076700508217 2508911117580057525381163)
          ·
            refine ⟨3763366676370086288071745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508911117580057525381163 3763366676370086288071745)
            ·
              refine ⟨2822525007277564716053809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3763366676370086288071745 2822525007277564716053809)
              ·
                refine ⟨2116893755458173537040357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822525007277564716053809 2116893755458173537040357)
                ·
                  refine ⟨396917579148407538195067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116893755458173537040357 396917579148407538195067)
                  ·
                    rfl

theorem cell21_1739237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_1739237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739237 prefixEnd_1739237 := by exact prefixLift 1739237
  have htrace : WordTrace (prefixWord ++ tailWord_1739237) baseStart_1739237 baseEnd_1739237 := by
    simpa [prefixWord, tailWord_1739237, baseEnd_1739237] using wordTrace_append hprefix tailTrace_1739237
  have hstable : (prefixWord ++ tailWord_1739237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739237).length < 2 ^ (prefixWord ++ tailWord_1739237).sum := by decide
  have hdescent : baseEnd_1739237 < baseStart_1739237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739248 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_1739248 : Nat := 118140960795 + 1739248 * 2 ^ 59
def prefixEnd_1739248 : Nat := 4983230072969 + 3 ^ 40 * 1739248 * 2
def baseEnd_1739248 : Nat := 396920089498273963511711

theorem tailTrace_1739248 : CollatzResearch.WordTrace tailWord_1739248 prefixEnd_1739248 396920089498273963511711 := by
  unfold tailWord_1739248
  simp only [CollatzResearch.WordTrace]
  refine ⟨31717793001504505377477199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42290390668672673836636265 31717793001504505377477199)
  ·
    refine ⟨47576689502256758066215799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31717793001504505377477199 47576689502256758066215799)
    ·
      refine ⟨71365034253385137099323699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47576689502256758066215799 71365034253385137099323699)
      ·
        refine ⟨107047551380077705648985549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71365034253385137099323699 107047551380077705648985549)
        ·
          refine ⟨40142831767529139618369581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107047551380077705648985549 40142831767529139618369581)
          ·
            refine ⟨15053561912823427356888593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40142831767529139618369581 15053561912823427356888593)
            ·
              refine ⟨11290171434617570517666445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15053561912823427356888593 11290171434617570517666445)
              ·
                refine ⟨4233814287981588944124917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11290171434617570517666445 4233814287981588944124917)
                ·
                  refine ⟨396920089498273963511711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4233814287981588944124917 396920089498273963511711)
                  ·
                    rfl

theorem cell21_1739248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_1739248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739248 prefixEnd_1739248 := by exact prefixLift 1739248
  have htrace : WordTrace (prefixWord ++ tailWord_1739248) baseStart_1739248 baseEnd_1739248 := by
    simpa [prefixWord, tailWord_1739248, baseEnd_1739248] using wordTrace_append hprefix tailTrace_1739248
  have hstable : (prefixWord ++ tailWord_1739248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739248).length < 2 ^ (prefixWord ++ tailWord_1739248).sum := by decide
  have hdescent : baseEnd_1739248 < baseStart_1739248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739265 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 5]
def baseStart_1739265 : Nat := 118140960795 + 1739265 * 2 ^ 59
def prefixEnd_1739265 : Nat := 4983230072969 + 3 ^ 40 * 1739265 * 2
def baseEnd_1739265 : Nat := 396923969129885711728343

theorem tailTrace_1739265 : CollatzResearch.WordTrace tailWord_1739265 prefixEnd_1739265 396923969129885711728343 := by
  unfold tailWord_1739265
  simp only [CollatzResearch.WordTrace]
  refine ⟨63436206043947422658323249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42290804029298281772215499 63436206043947422658323249)
  ·
    refine ⟨47577154532960566993742437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63436206043947422658323249 47577154532960566993742437)
    ·
      refine ⟨8920716474930106311326707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47577154532960566993742437 8920716474930106311326707)
      ·
        refine ⟨13381074712395159466990061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8920716474930106311326707 13381074712395159466990061)
        ·
          refine ⟨5017903017148184800121273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13381074712395159466990061 5017903017148184800121273)
          ·
            refine ⟨3763427262861138600090955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5017903017148184800121273 3763427262861138600090955)
            ·
              refine ⟨5645140894291707900136433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763427262861138600090955 5645140894291707900136433)
              ·
                refine ⟨4233855670718780925102325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5645140894291707900136433 4233855670718780925102325)
                ·
                  refine ⟨396923969129885711728343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4233855670718780925102325 396923969129885711728343)
                  ·
                    rfl

theorem cell21_1739265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_1739265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739265 prefixEnd_1739265 := by exact prefixLift 1739265
  have htrace : WordTrace (prefixWord ++ tailWord_1739265) baseStart_1739265 baseEnd_1739265 := by
    simpa [prefixWord, tailWord_1739265, baseEnd_1739265] using wordTrace_append hprefix tailTrace_1739265
  have hstable : (prefixWord ++ tailWord_1739265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739265).length < 2 ^ (prefixWord ++ tailWord_1739265).sum := by decide
  have hdescent : baseEnd_1739265 < baseStart_1739265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739296 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_1739296 : Nat := 118140960795 + 1739296 * 2 ^ 59
def prefixEnd_1739296 : Nat := 4983230072969 + 3 ^ 40 * 1739296 * 2
def baseEnd_1739296 : Nat := 396931043752236546711613

theorem tailTrace_1739296 : CollatzResearch.WordTrace tailWord_1739296 prefixEnd_1739296 396931043752236546711613 := by
  unfold tailWord_1739296
  simp only [CollatzResearch.WordTrace]
  refine ⟨31718668353417557476350871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42291557804556743301801161 31718668353417557476350871)
  ·
    refine ⟨47578002530126336214526307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31718668353417557476350871 47578002530126336214526307)
    ·
      refine ⟨71367003795189504321789461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47578002530126336214526307 71367003795189504321789461)
      ·
        refine ⟨3345328302899508015083881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71367003795189504321789461 3345328302899508015083881)
        ·
          refine ⟨2508996227174631011312911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3345328302899508015083881 2508996227174631011312911)
          ·
            refine ⟨3763494340761946516969367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508996227174631011312911 3763494340761946516969367)
            ·
              refine ⟨5645241511142919775454051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763494340761946516969367 5645241511142919775454051)
              ·
                refine ⟨8467862266714379663181077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645241511142919775454051 8467862266714379663181077)
                ·
                  refine ⟨396931043752236546711613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8467862266714379663181077 396931043752236546711613)
                  ·
                    rfl

theorem cell21_1739296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_1739296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739296 prefixEnd_1739296 := by exact prefixLift 1739296
  have htrace : WordTrace (prefixWord ++ tailWord_1739296) baseStart_1739296 baseEnd_1739296 := by
    simpa [prefixWord, tailWord_1739296, baseEnd_1739296] using wordTrace_append hprefix tailTrace_1739296
  have hstable : (prefixWord ++ tailWord_1739296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739296).length < 2 ^ (prefixWord ++ tailWord_1739296).sum := by decide
  have hdescent : baseEnd_1739296 < baseStart_1739296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739372 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_1739372 : Nat := 118140960795 + 1739372 * 2 ^ 59
def prefixEnd_1739372 : Nat := 4983230072969 + 3 ^ 40 * 1739372 * 2
def baseEnd_1739372 : Nat := 396948387987677303444791

theorem tailTrace_1739372 : CollatzResearch.WordTrace tailWord_1739372 prefixEnd_1739372 396948387987677303444791 := by
  unfold tailWord_1739372
  simp only [CollatzResearch.WordTrace]
  refine ⟨31720054327279889966234185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42293405769706519954978913 31720054327279889966234185)
  ·
    refine ⟨23790040745459917474675639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31720054327279889966234185 23790040745459917474675639)
    ·
      refine ⟨35685061118189876212013459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23790040745459917474675639 35685061118189876212013459)
      ·
        refine ⟨53527591677284814318020189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35685061118189876212013459 53527591677284814318020189)
        ·
          refine ⟨20072846878981805369257571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53527591677284814318020189 20072846878981805369257571)
          ·
            refine ⟨30109270318472708053886357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20072846878981805369257571 30109270318472708053886357)
            ·
              refine ⟨1411372046178408190025923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30109270318472708053886357 1411372046178408190025923)
              ·
                refine ⟨2117058069267612285038885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411372046178408190025923 2117058069267612285038885)
                ·
                  refine ⟨396948387987677303444791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117058069267612285038885 396948387987677303444791)
                  ·
                    rfl

theorem cell21_1739372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_1739372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739372 prefixEnd_1739372 := by exact prefixLift 1739372
  have htrace : WordTrace (prefixWord ++ tailWord_1739372) baseStart_1739372 baseEnd_1739372 := by
    simpa [prefixWord, tailWord_1739372, baseEnd_1739372] using wordTrace_append hprefix tailTrace_1739372
  have hstable : (prefixWord ++ tailWord_1739372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739372).length < 2 ^ (prefixWord ++ tailWord_1739372).sum := by decide
  have hdescent : baseEnd_1739372 < baseStart_1739372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739417 : List Nat := [1, 2, 1, 2, 1, 2, 5, 4, 3]
def baseStart_1739417 : Nat := 118140960795 + 1739417 * 2 ^ 59
def prefixEnd_1739417 : Nat := 4983230072969 + 3 ^ 40 * 1739417 * 2
def baseEnd_1739417 : Nat := 396958657600767225194699

theorem tailTrace_1739417 : CollatzResearch.WordTrace tailWord_1739417 prefixEnd_1739417 396958657600767225194699 := by
  unfold tailWord_1739417
  simp only [CollatzResearch.WordTrace]
  refine ⟨63441749939396752617856505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42294499959597835078571003 63441749939396752617856505)
  ·
    refine ⟨47581312454547564463392379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63441749939396752617856505 47581312454547564463392379)
    ·
      refine ⟨71371968681821346695088569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47581312454547564463392379 71371968681821346695088569)
      ·
        refine ⟨53528976511366010021316427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71371968681821346695088569 53528976511366010021316427)
        ·
          refine ⟨80293464767049015031974641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53528976511366010021316427 80293464767049015031974641)
          ·
            refine ⟨60220098575286761273980981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80293464767049015031974641 60220098575286761273980981)
            ·
              refine ⟨5645634241433133869435717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60220098575286761273980981 5645634241433133869435717)
              ·
                refine ⟨1058556420268712600519197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5645634241433133869435717 1058556420268712600519197)
                ·
                  refine ⟨396958657600767225194699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058556420268712600519197 396958657600767225194699)
                  ·
                    rfl

theorem cell21_1739417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_1739417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739417 prefixEnd_1739417 := by exact prefixLift 1739417
  have htrace : WordTrace (prefixWord ++ tailWord_1739417) baseStart_1739417 baseEnd_1739417 := by
    simpa [prefixWord, tailWord_1739417, baseEnd_1739417] using wordTrace_append hprefix tailTrace_1739417
  have hstable : (prefixWord ++ tailWord_1739417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739417).length < 2 ^ (prefixWord ++ tailWord_1739417).sum := by decide
  have hdescent : baseEnd_1739417 < baseStart_1739417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739496 : List Nat := [2, 1, 4, 1, 5, 1, 2, 5]
def baseStart_1739496 : Nat := 118140960795 + 1739496 * 2 ^ 59
def prefixEnd_1739496 : Nat := 4983230072969 + 3 ^ 40 * 1739496 * 2
def baseEnd_1739496 : Nat := 132325562159026881125957

theorem tailTrace_1739496 : CollatzResearch.WordTrace tailWord_1739496 prefixEnd_1739496 132325562159026881125957 := by
  unfold tailWord_1739496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31722315653055274554991171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42296420870740366073321561 31722315653055274554991171)
  ·
    refine ⟨47583473479582911832486757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31722315653055274554991171 47583473479582911832486757)
    ·
      refine ⟨8921901277421795968591267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47583473479582911832486757 8921901277421795968591267)
      ·
        refine ⟨13382851916132693952886901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8921901277421795968591267 13382851916132693952886901)
        ·
          refine ⟨1254642367137440058083147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13382851916132693952886901 1254642367137440058083147)
          ·
            refine ⟨1881963550706160087124721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254642367137440058083147 1881963550706160087124721)
            ·
              refine ⟨1411472663029620065343541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881963550706160087124721 1411472663029620065343541)
              ·
                refine ⟨132325562159026881125957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1411472663029620065343541 132325562159026881125957)
                ·
                  rfl

theorem cell21_1739496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_1739496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739496 prefixEnd_1739496 := by exact prefixLift 1739496
  have htrace : WordTrace (prefixWord ++ tailWord_1739496) baseStart_1739496 baseEnd_1739496 := by
    simpa [prefixWord, tailWord_1739496, baseEnd_1739496] using wordTrace_append hprefix tailTrace_1739496
  have hstable : (prefixWord ++ tailWord_1739496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739496).length < 2 ^ (prefixWord ++ tailWord_1739496).sum := by decide
  have hdescent : baseEnd_1739496 < baseStart_1739496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739527 : List Nat := [1, 1, 4, 4, 1, 2, 3, 2, 3]
def baseStart_1739527 : Nat := 118140960795 + 1739527 * 2 ^ 59
def prefixEnd_1739527 : Nat := 4983230072969 + 3 ^ 40 * 1739527 * 2
def baseEnd_1739527 : Nat := 396983761099431478361141

theorem tailTrace_1739527 : CollatzResearch.WordTrace tailWord_1739527 prefixEnd_1739527 396983761099431478361141 := by
  unfold tailWord_1739527
  simp only [CollatzResearch.WordTrace]
  refine ⟨63445761968998241404360835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42297174645998827602907223 63445761968998241404360835)
  ·
    refine ⟨95168642953497362106541253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63445761968998241404360835 95168642953497362106541253)
    ·
      refine ⟨17844120553780755394976485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95168642953497362106541253 17844120553780755394976485)
      ·
        refine ⟨3345772603833891636558091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17844120553780755394976485 3345772603833891636558091)
        ·
          refine ⟨5018658905750837454837137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3345772603833891636558091 5018658905750837454837137)
          ·
            refine ⟨3763994179313128091127853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5018658905750837454837137 3763994179313128091127853)
            ·
              refine ⟨1411497817242423034172945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3763994179313128091127853 1411497817242423034172945)
              ·
                refine ⟨1058623362931817275629709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411497817242423034172945 1058623362931817275629709)
                ·
                  refine ⟨396983761099431478361141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058623362931817275629709 396983761099431478361141)
                  ·
                    rfl

theorem cell21_1739527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 3].length) (baseStart_1739527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739527 prefixEnd_1739527 := by exact prefixLift 1739527
  have htrace : WordTrace (prefixWord ++ tailWord_1739527) baseStart_1739527 baseEnd_1739527 := by
    simpa [prefixWord, tailWord_1739527, baseEnd_1739527] using wordTrace_append hprefix tailTrace_1739527
  have hstable : (prefixWord ++ tailWord_1739527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739527).length < 2 ^ (prefixWord ++ tailWord_1739527).sum := by decide
  have hdescent : baseEnd_1739527 < baseStart_1739527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739569 : List Nat := [1, 2, 2, 3, 2, 1, 2, 5, 3]
def baseStart_1739569 : Nat := 118140960795 + 1739569 * 2 ^ 59
def prefixEnd_1739569 : Nat := 4983230072969 + 3 ^ 40 * 1739569 * 2
def baseEnd_1739569 : Nat := 396993346071648738661055

theorem tailTrace_1739569 : CollatzResearch.WordTrace tailWord_1739569 prefixEnd_1739569 396993346071648738661055 := by
  unfold tailWord_1739569
  simp only [CollatzResearch.WordTrace]
  refine ⟨63447293834846082577389761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42298195889897388384926507 63447293834846082577389761)
  ·
    refine ⟨47585470376134561933042321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63447293834846082577389761 47585470376134561933042321)
    ·
      refine ⟨35689102782100921449781741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47585470376134561933042321 35689102782100921449781741)
      ·
        refine ⟨13383413543287845543668153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35689102782100921449781741 13383413543287845543668153)
        ·
          refine ⟨10037560157465884157751115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13383413543287845543668153 10037560157465884157751115)
          ·
            refine ⟨15056340236198826236626673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10037560157465884157751115 15056340236198826236626673)
            ·
              refine ⟨11292255177149119677470005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15056340236198826236626673 11292255177149119677470005)
              ·
                refine ⟨1058648922857729969762813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11292255177149119677470005 1058648922857729969762813)
                ·
                  refine ⟨396993346071648738661055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058648922857729969762813 396993346071648738661055)
                  ·
                    rfl

theorem cell21_1739569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_1739569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739569 prefixEnd_1739569 := by exact prefixLift 1739569
  have htrace : WordTrace (prefixWord ++ tailWord_1739569) baseStart_1739569 baseEnd_1739569 := by
    simpa [prefixWord, tailWord_1739569, baseEnd_1739569] using wordTrace_append hprefix tailTrace_1739569
  have hstable : (prefixWord ++ tailWord_1739569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739569).length < 2 ^ (prefixWord ++ tailWord_1739569).sum := by decide
  have hdescent : baseEnd_1739569 < baseStart_1739569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739583 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 4]
def baseStart_1739583 : Nat := 118140960795 + 1739583 * 2 ^ 59
def prefixEnd_1739583 : Nat := 4983230072969 + 3 ^ 40 * 1739583 * 2
def baseEnd_1739583 : Nat := 396996541062387825427693

theorem tailTrace_1739583 : CollatzResearch.WordTrace tailWord_1739583 prefixEnd_1739583 396996541062387825427693 := by
  unfold tailWord_1739583
  simp only [CollatzResearch.WordTrace]
  refine ⟨63447804456795362968399403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42298536304530241978932935 63447804456795362968399403)
  ·
    refine ⟨95171706685193044452599105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63447804456795362968399403 95171706685193044452599105)
    ·
      refine ⟨71378780013894783339449329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95171706685193044452599105 71378780013894783339449329)
      ·
        refine ⟨53534085010421087504586997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71378780013894783339449329 53534085010421087504586997)
        ·
          refine ⟨5018820469726976953555031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53534085010421087504586997 5018820469726976953555031)
          ·
            refine ⟨7528230704590465430332547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5018820469726976953555031 7528230704590465430332547)
            ·
              refine ⟨11292346056885698145498821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7528230704590465430332547 11292346056885698145498821)
              ·
                refine ⟨2117314885666068402281029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11292346056885698145498821 2117314885666068402281029)
                ·
                  refine ⟨396996541062387825427693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117314885666068402281029 396996541062387825427693)
                  ·
                    rfl

theorem cell21_1739583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 4].length) (baseStart_1739583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739583 prefixEnd_1739583 := by exact prefixLift 1739583
  have htrace : WordTrace (prefixWord ++ tailWord_1739583) baseStart_1739583 baseEnd_1739583 := by
    simpa [prefixWord, tailWord_1739583, baseEnd_1739583] using wordTrace_append hprefix tailTrace_1739583
  have hstable : (prefixWord ++ tailWord_1739583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739583).length < 2 ^ (prefixWord ++ tailWord_1739583).sum := by decide
  have hdescent : baseEnd_1739583 < baseStart_1739583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739645 : List Nat := [1, 4, 1, 1, 2, 1, 4, 4, 3]
def baseStart_1739645 : Nat := 118140960795 + 1739645 * 2 ^ 59
def prefixEnd_1739645 : Nat := 4983230072969 + 3 ^ 40 * 1739645 * 2
def baseEnd_1739645 : Nat := 397010690307089495394233

theorem tailTrace_1739645 : CollatzResearch.WordTrace tailWord_1739645 prefixEnd_1739645 397010690307089495394233 := by
  unfold tailWord_1739645
  simp only [CollatzResearch.WordTrace]
  refine ⟨63450065782570747557156389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42300043855047165038104259 63450065782570747557156389)
  ·
    refine ⟨11896887334232015166966823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63450065782570747557156389 11896887334232015166966823)
    ·
      refine ⟨17845331001348022750450235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11896887334232015166966823 17845331001348022750450235)
      ·
        refine ⟨26767996502022034125675353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17845331001348022750450235 26767996502022034125675353)
        ·
          refine ⟨20075997376516525594256515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26767996502022034125675353 20075997376516525594256515)
          ·
            refine ⟨30113996064774788391384773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20075997376516525594256515 30113996064774788391384773)
            ·
              refine ⟨5646374262145272823384645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30113996064774788391384773 5646374262145272823384645)
              ·
                refine ⟨1058695174152238654384621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5646374262145272823384645 1058695174152238654384621)
                ·
                  refine ⟨397010690307089495394233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058695174152238654384621 397010690307089495394233)
                  ·
                    rfl

theorem cell21_1739645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_1739645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739645 prefixEnd_1739645 := by exact prefixLift 1739645
  have htrace : WordTrace (prefixWord ++ tailWord_1739645) baseStart_1739645 baseEnd_1739645 := by
    simpa [prefixWord, tailWord_1739645, baseEnd_1739645] using wordTrace_append hprefix tailTrace_1739645
  have hstable : (prefixWord ++ tailWord_1739645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739645).length < 2 ^ (prefixWord ++ tailWord_1739645).sum := by decide
  have hdescent : baseEnd_1739645 < baseStart_1739645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739704 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_1739704 : Nat := 118140960795 + 1739704 * 2 ^ 59
def prefixEnd_1739704 : Nat := 4983230072969 + 3 ^ 40 * 1739704 * 2
def baseEnd_1739704 : Nat := 397024154910918503910779

theorem tailTrace_1739704 : CollatzResearch.WordTrace tailWord_1739704 prefixEnd_1739704 397024154910918503910779 := by
  unfold tailWord_1739704
  simp only [CollatzResearch.WordTrace]
  refine ⟨31726108844678500316777083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42301478459571333755702777 31726108844678500316777083)
  ·
    refine ⟨47589163267017750475165625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31726108844678500316777083 47589163267017750475165625)
    ·
      refine ⟨35691872450263312856374219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47589163267017750475165625 35691872450263312856374219)
      ·
        refine ⟨53537808675394969284561329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35691872450263312856374219 53537808675394969284561329)
        ·
          refine ⟨40153356506546226963420997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53537808675394969284561329 40153356506546226963420997)
          ·
            refine ⟨7528754344977417555641437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40153356506546226963420997 7528754344977417555641437)
            ·
              refine ⟨2823282879366531583365539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7528754344977417555641437 2823282879366531583365539)
              ·
                refine ⟨4234924319049797375048309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823282879366531583365539 4234924319049797375048309)
                ·
                  refine ⟨397024154910918503910779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4234924319049797375048309 397024154910918503910779)
                  ·
                    rfl

theorem cell21_1739704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_1739704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739704 prefixEnd_1739704 := by exact prefixLift 1739704
  have htrace : WordTrace (prefixWord ++ tailWord_1739704) baseStart_1739704 baseEnd_1739704 := by
    simpa [prefixWord, tailWord_1739704, baseEnd_1739704] using wordTrace_append hprefix tailTrace_1739704
  have hstable : (prefixWord ++ tailWord_1739704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739704).length < 2 ^ (prefixWord ++ tailWord_1739704).sum := by decide
  have hdescent : baseEnd_1739704 < baseStart_1739704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739749 : List Nat := [1, 3, 1, 6, 10]
def baseStart_1739749 : Nat := 118140960795 + 1739749 * 2 ^ 59
def prefixEnd_1739749 : Nat := 4983230072969 + 3 ^ 40 * 1739749 * 2
def baseEnd_1739749 : Nat := 4901659562024795378527

theorem tailTrace_1739749 : CollatzResearch.WordTrace tailWord_1739749 prefixEnd_1739749 4901659562024795378527 := by
  unfold tailWord_1739749
  simp only [CollatzResearch.WordTrace]
  refine ⟨63453858974193973318942301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42302572649462648879294867 63453858974193973318942301)
  ·
    refine ⟨23795197115322739994603363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63453858974193973318942301 23795197115322739994603363)
    ·
      refine ⟨35692795672984109991905045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23795197115322739994603363 35692795672984109991905045)
      ·
        refine ⟨1673099797171130155870549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35692795672984109991905045 1673099797171130155870549)
        ·
          refine ⟨4901659562024795378527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1673099797171130155870549 4901659562024795378527)
          ·
            rfl

theorem cell21_1739749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 10].length) (baseStart_1739749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739749 prefixEnd_1739749 := by exact prefixLift 1739749
  have htrace : WordTrace (prefixWord ++ tailWord_1739749) baseStart_1739749 baseEnd_1739749 := by
    simpa [prefixWord, tailWord_1739749, baseEnd_1739749] using wordTrace_append hprefix tailTrace_1739749
  have hstable : (prefixWord ++ tailWord_1739749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739749).length < 2 ^ (prefixWord ++ tailWord_1739749).sum := by decide
  have hdescent : baseEnd_1739749 < baseStart_1739749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739766 : List Nat := [5, 1, 1, 1, 3, 1, 3, 6]
def baseStart_1739766 : Nat := 118140960795 + 1739766 * 2 ^ 59
def prefixEnd_1739766 : Nat := 4983230072969 + 3 ^ 40 * 1739766 * 2
def baseEnd_1739766 : Nat := 132346101385206724625773

theorem tailTrace_1739766 : CollatzResearch.WordTrace tailWord_1739766 prefixEnd_1739766 132346101385206724625773 := by
  unfold tailWord_1739766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965904938445774076394447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42302986010088256814874101 3965904938445774076394447)
  ·
    refine ⟨5948857407668661114591671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3965904938445774076394447 5948857407668661114591671)
    ·
      refine ⟨8923286111502991671887507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5948857407668661114591671 8923286111502991671887507)
      ·
        refine ⟨13384929167254487507831261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8923286111502991671887507 13384929167254487507831261)
        ·
          refine ⟨5019348437720432815436723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13384929167254487507831261 5019348437720432815436723)
          ·
            refine ⟨7529022656580649223155085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019348437720432815436723 7529022656580649223155085)
            ·
              refine ⟨2823383496217743458683157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7529022656580649223155085 2823383496217743458683157)
              ·
                refine ⟨132346101385206724625773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2823383496217743458683157 132346101385206724625773)
                ·
                  rfl

theorem cell21_1739766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_1739766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739766 prefixEnd_1739766 := by exact prefixLift 1739766
  have htrace : WordTrace (prefixWord ++ tailWord_1739766) baseStart_1739766 baseEnd_1739766 := by
    simpa [prefixWord, tailWord_1739766, baseEnd_1739766] using wordTrace_append hprefix tailTrace_1739766
  have hstable : (prefixWord ++ tailWord_1739766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739766).length < 2 ^ (prefixWord ++ tailWord_1739766).sum := by decide
  have hdescent : baseEnd_1739766 < baseStart_1739766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739797 : List Nat := [1, 3, 2, 1, 4, 1, 1, 5, 3]
def baseStart_1739797 : Nat := 118140960795 + 1739797 * 2 ^ 59
def prefixEnd_1739797 : Nat := 4983230072969 + 3 ^ 40 * 1739797 * 2
def baseEnd_1739797 : Nat := 397045378777971008860589

theorem tailTrace_1739797 : CollatzResearch.WordTrace tailWord_1739797 prefixEnd_1739797 397045378777971008860589 := by
  unfold tailWord_1739797
  simp only [CollatzResearch.WordTrace]
  refine ⟨63455609678020077516689645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42303739785346718344459763 63455609678020077516689645)
  ·
    refine ⟨23795853629257529068758617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63455609678020077516689645 23795853629257529068758617)
    ·
      refine ⟨17846890221943146801568963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23795853629257529068758617 17846890221943146801568963)
      ·
        refine ⟨26770335332914720202353445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17846890221943146801568963 26770335332914720202353445)
        ·
          refine ⟨5019437874921510037941271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26770335332914720202353445 5019437874921510037941271)
          ·
            refine ⟨7529156812382265056911907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5019437874921510037941271 7529156812382265056911907)
            ·
              refine ⟨11293735218573397585367861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7529156812382265056911907 11293735218573397585367861)
              ·
                refine ⟨1058787676741256023628237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11293735218573397585367861 1058787676741256023628237)
                ·
                  refine ⟨397045378777971008860589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058787676741256023628237 397045378777971008860589)
                  ·
                    rfl

theorem cell21_1739797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_1739797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739797 prefixEnd_1739797 := by exact prefixLift 1739797
  have htrace : WordTrace (prefixWord ++ tailWord_1739797) baseStart_1739797 baseEnd_1739797 := by
    simpa [prefixWord, tailWord_1739797, baseEnd_1739797] using wordTrace_append hprefix tailTrace_1739797
  have hstable : (prefixWord ++ tailWord_1739797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739797).length < 2 ^ (prefixWord ++ tailWord_1739797).sum := by decide
  have hdescent : baseEnd_1739797 < baseStart_1739797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739811 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 4]
def baseStart_1739811 : Nat := 118140960795 + 1739811 * 2 ^ 59
def prefixEnd_1739811 : Nat := 4983230072969 + 3 ^ 40 * 1739811 * 2
def baseEnd_1739811 : Nat := 397048573768710095627227

theorem tailTrace_1739811 : CollatzResearch.WordTrace tailWord_1739811 prefixEnd_1739811 397048573768710095627227 := by
  unfold tailWord_1739811
  simp only [CollatzResearch.WordTrace]
  refine ⟨63456120299969357907699287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42304080199979571938466191 63456120299969357907699287)
  ·
    refine ⟨95184180449954036861548931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63456120299969357907699287 95184180449954036861548931)
    ·
      refine ⟨142776270674931055292323397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95184180449954036861548931 142776270674931055292323397)
      ·
        refine ⟨26770550751549572867310637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142776270674931055292323397 26770550751549572867310637)
        ·
          refine ⟨10038956531831089825241489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26770550751549572867310637 10038956531831089825241489)
          ·
            refine ⟨7529217398873317368931117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10038956531831089825241489 7529217398873317368931117)
            ·
              refine ⟨2823456524577494013349169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7529217398873317368931117 2823456524577494013349169)
              ·
                refine ⟨2117592393433120510011877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2823456524577494013349169 2117592393433120510011877)
                ·
                  refine ⟨397048573768710095627227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117592393433120510011877 397048573768710095627227)
                  ·
                    rfl

theorem cell21_1739811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 4].length) (baseStart_1739811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739811 prefixEnd_1739811 := by exact prefixLift 1739811
  have htrace : WordTrace (prefixWord ++ tailWord_1739811) baseStart_1739811 baseEnd_1739811 := by
    simpa [prefixWord, tailWord_1739811, baseEnd_1739811] using wordTrace_append hprefix tailTrace_1739811
  have hstable : (prefixWord ++ tailWord_1739811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739811).length < 2 ^ (prefixWord ++ tailWord_1739811).sum := by decide
  have hdescent : baseEnd_1739811 < baseStart_1739811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739935 : List Nat := [1, 1, 2, 6, 3, 1, 1, 6]
def baseStart_1739935 : Nat := 118140960795 + 1739935 * 2 ^ 59
def prefixEnd_1739935 : Nat := 4983230072969 + 3 ^ 40 * 1739935 * 2
def baseEnd_1739935 : Nat := 132358957419371145186769

theorem tailTrace_1739935 : CollatzResearch.WordTrace tailWord_1739935 prefixEnd_1739935 132358957419371145186769 := by
  unfold tailWord_1739935
  simp only [CollatzResearch.WordTrace]
  refine ⟨63460642951520127085213259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42307095301013418056808839 63460642951520127085213259)
  ·
    refine ⟨95190964427280190627819889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63460642951520127085213259 95190964427280190627819889)
    ·
      refine ⟨71393223320460142970864917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95190964427280190627819889 71393223320460142970864917)
      ·
        refine ⟨3346557343146569201759293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71393223320460142970864917 3346557343146569201759293)
        ·
          refine ⟨1254959003679963450659735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3346557343146569201759293 1254959003679963450659735)
          ·
            refine ⟨1882438505519945175989603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254959003679963450659735 1882438505519945175989603)
            ·
              refine ⟨2823657758279917763984405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882438505519945175989603 2823657758279917763984405)
              ·
                refine ⟨132358957419371145186769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2823657758279917763984405 132358957419371145186769)
                ·
                  rfl

theorem cell21_1739935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 6].length) (baseStart_1739935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739935 prefixEnd_1739935 := by exact prefixLift 1739935
  have htrace : WordTrace (prefixWord ++ tailWord_1739935) baseStart_1739935 baseEnd_1739935 := by
    simpa [prefixWord, tailWord_1739935, baseEnd_1739935] using wordTrace_append hprefix tailTrace_1739935
  have hstable : (prefixWord ++ tailWord_1739935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739935).length < 2 ^ (prefixWord ++ tailWord_1739935).sum := by decide
  have hdescent : baseEnd_1739935 < baseStart_1739935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739949 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1739949 : Nat := 118140960795 + 1739949 * 2 ^ 59
def prefixEnd_1739949 : Nat := 4983230072969 + 3 ^ 40 * 1739949 * 2
def baseEnd_1739949 : Nat := 397080067248852522326945

theorem tailTrace_1739949 : CollatzResearch.WordTrace tailWord_1739949 prefixEnd_1739949 397080067248852522326945 := by
  unfold tailWord_1739949
  simp only [CollatzResearch.WordTrace]
  refine ⟨63461153573469407476222901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42307435715646271650815267 63461153573469407476222901)
  ·
    refine ⟨5949483147512756950895897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63461153573469407476222901 5949483147512756950895897)
    ·
      refine ⟨4462112360634567713171923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5949483147512756950895897 4462112360634567713171923)
      ·
        refine ⟨6693168540951851569757885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4462112360634567713171923 6693168540951851569757885)
        ·
          refine ⟨2509938202856944338659207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6693168540951851569757885 2509938202856944338659207)
          ·
            refine ⟨3764907304285416507988811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509938202856944338659207 3764907304285416507988811)
            ·
              refine ⟨5647360956428124761983217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764907304285416507988811 5647360956428124761983217)
              ·
                refine ⟨4235520717321093571487413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5647360956428124761983217 4235520717321093571487413)
                ·
                  refine ⟨397080067248852522326945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4235520717321093571487413 397080067248852522326945)
                  ·
                    rfl

theorem cell21_1739949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1739949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739949 prefixEnd_1739949 := by exact prefixLift 1739949
  have htrace : WordTrace (prefixWord ++ tailWord_1739949) baseStart_1739949 baseEnd_1739949 := by
    simpa [prefixWord, tailWord_1739949, baseEnd_1739949] using wordTrace_append hprefix tailTrace_1739949
  have hstable : (prefixWord ++ tailWord_1739949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739949).length < 2 ^ (prefixWord ++ tailWord_1739949).sum := by decide
  have hdescent : baseEnd_1739949 < baseStart_1739949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739966 : List Nat := [4, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_1739966 : Nat := 118140960795 + 1739966 * 2 ^ 59
def prefixEnd_1739966 : Nat := 4983230072969 + 3 ^ 40 * 1739966 * 2
def baseEnd_1739966 : Nat := 397083946880464270543577

theorem tailTrace_1739966 : CollatzResearch.WordTrace tailWord_1739966 prefixEnd_1739966 397083946880464270543577 := by
  unfold tailWord_1739966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7932721701800977422448969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42307849076271879586394501 7932721701800977422448969)
  ·
    refine ⟨5949541276350733066836727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7932721701800977422448969 5949541276350733066836727)
    ·
      refine ⟨8924311914526099600255091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5949541276350733066836727 8924311914526099600255091)
      ·
        refine ⟨13386467871789149400382637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924311914526099600255091 13386467871789149400382637)
        ·
          refine ⟨5019925451920931025143489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13386467871789149400382637 5019925451920931025143489)
          ·
            refine ⟨3764944088940698268857617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5019925451920931025143489 3764944088940698268857617)
            ·
              refine ⟨2823708066705523701643213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764944088940698268857617 2823708066705523701643213)
              ·
                refine ⟨1058890525014571388116205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2823708066705523701643213 1058890525014571388116205)
                ·
                  refine ⟨397083946880464270543577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058890525014571388116205 397083946880464270543577)
                  ·
                    rfl

theorem cell21_1739966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_1739966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739966 prefixEnd_1739966 := by exact prefixLift 1739966
  have htrace : WordTrace (prefixWord ++ tailWord_1739966) baseStart_1739966 baseEnd_1739966 := by
    simpa [prefixWord, tailWord_1739966, baseEnd_1739966] using wordTrace_append hprefix tailTrace_1739966
  have hstable : (prefixWord ++ tailWord_1739966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739966).length < 2 ^ (prefixWord ++ tailWord_1739966).sum := by decide
  have hdescent : baseEnd_1739966 < baseStart_1739966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739991 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 5]
def baseStart_1739991 : Nat := 118140960795 + 1739991 * 2 ^ 59
def prefixEnd_1739991 : Nat := 4983230072969 + 3 ^ 40 * 1739991 * 2
def baseEnd_1739991 : Nat := 397089652221069782626859

theorem tailTrace_1739991 : CollatzResearch.WordTrace tailWord_1739991 prefixEnd_1739991 397089652221069782626859 := by
  unfold tailWord_1739991
  simp only [CollatzResearch.WordTrace]
  refine ⟨63462685439317248649251827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42308456959544832432834551 63462685439317248649251827)
  ·
    refine ⟨95194028158975872973877741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63462685439317248649251827 95194028158975872973877741)
    ·
      refine ⟨35697760559615952365204153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95194028158975872973877741 35697760559615952365204153)
      ·
        refine ⟨26773320419711964273903115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35697760559615952365204153 26773320419711964273903115)
        ·
          refine ⟨40159980629567946410854673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26773320419711964273903115 40159980629567946410854673)
          ·
            refine ⟨30119985472175959808141005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40159980629567946410854673 30119985472175959808141005)
            ·
              refine ⟨11294994552065984928052877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30119985472175959808141005 11294994552065984928052877)
              ·
                refine ⟨4235622957024744348019829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11294994552065984928052877 4235622957024744348019829)
                ·
                  refine ⟨397089652221069782626859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4235622957024744348019829 397089652221069782626859)
                  ·
                    rfl

theorem cell21_1739991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_1739991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739991 prefixEnd_1739991 := by exact prefixLift 1739991
  have htrace : WordTrace (prefixWord ++ tailWord_1739991) baseStart_1739991 baseEnd_1739991 := by
    simpa [prefixWord, tailWord_1739991, baseEnd_1739991] using wordTrace_append hprefix tailTrace_1739991
  have hstable : (prefixWord ++ tailWord_1739991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739991).length < 2 ^ (prefixWord ++ tailWord_1739991).sum := by decide
  have hdescent : baseEnd_1739991 < baseStart_1739991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1739997 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1739997 : Nat := 118140960795 + 1739997 * 2 ^ 59
def prefixEnd_1739997 : Nat := 4983230072969 + 3 ^ 40 * 1739997 * 2
def baseEnd_1739997 : Nat := 397091021502815105526847

theorem tailTrace_1739997 : CollatzResearch.WordTrace tailWord_1739997 prefixEnd_1739997 397091021502815105526847 := by
  unfold tailWord_1739997
  simp only [CollatzResearch.WordTrace]
  refine ⟨63462904277295511673970245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42308602851530341115980163 63462904277295511673970245)
  ·
    refine ⟨11899294551992908438869421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63462904277295511673970245 11899294551992908438869421)
    ·
      refine ⟨4462235456997340664576033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11899294551992908438869421 4462235456997340664576033)
      ·
        refine ⟨3346676592748005498432025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4462235456997340664576033 3346676592748005498432025)
        ·
          refine ⟨2510007444561004123824019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3346676592748005498432025 2510007444561004123824019)
          ·
            refine ⟨3765011166841506185736029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510007444561004123824019 3765011166841506185736029)
            ·
              refine ⟨1411879187565564819651011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3765011166841506185736029 1411879187565564819651011)
              ·
                refine ⟨2117818781348347229476517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411879187565564819651011 2117818781348347229476517)
                ·
                  refine ⟨397091021502815105526847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117818781348347229476517 397091021502815105526847)
                  ·
                    rfl

theorem cell21_1739997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1739997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1739997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1739997 prefixEnd_1739997 := by exact prefixLift 1739997
  have htrace : WordTrace (prefixWord ++ tailWord_1739997) baseStart_1739997 baseEnd_1739997 := by
    simpa [prefixWord, tailWord_1739997, baseEnd_1739997] using wordTrace_append hprefix tailTrace_1739997
  have hstable : (prefixWord ++ tailWord_1739997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1739997).length < 2 ^ (prefixWord ++ tailWord_1739997).sum := by decide
  have hdescent : baseEnd_1739997 < baseStart_1739997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1739997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740056 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_1740056 : Nat := 118140960795 + 1740056 * 2 ^ 59
def prefixEnd_1740056 : Nat := 4983230072969 + 3 ^ 40 * 1740056 * 2
def baseEnd_1740056 : Nat := 397104486106644114043393

theorem tailTrace_1740056 : CollatzResearch.WordTrace tailWord_1740056 prefixEnd_1740056 397104486106644114043393 := by
  unfold tailWord_1740056
  simp only [CollatzResearch.WordTrace]
  refine ⟨31732528092040882375184011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42310037456054509833578681 31732528092040882375184011)
  ·
    refine ⟨47598792138061323562776017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31732528092040882375184011 47598792138061323562776017)
    ·
      refine ⟨35699094103545992672082013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47598792138061323562776017 35699094103545992672082013)
      ·
        refine ⟨13387160288829747252030755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35699094103545992672082013 13387160288829747252030755)
        ·
          refine ⟨20080740433244620878046133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13387160288829747252030755 20080740433244620878046133)
          ·
            refine ⟨1882569415616683207316825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20080740433244620878046133 1882569415616683207316825)
            ·
              refine ⟨1411927061712512405487619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882569415616683207316825 1411927061712512405487619)
              ·
                refine ⟨2117890592568768608231429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411927061712512405487619 2117890592568768608231429)
                ·
                  refine ⟨397104486106644114043393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117890592568768608231429 397104486106644114043393)
                  ·
                    rfl

theorem cell21_1740056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_1740056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740056 prefixEnd_1740056 := by exact prefixLift 1740056
  have htrace : WordTrace (prefixWord ++ tailWord_1740056) baseStart_1740056 baseEnd_1740056 := by
    simpa [prefixWord, tailWord_1740056, baseEnd_1740056] using wordTrace_append hprefix tailTrace_1740056
  have hstable : (prefixWord ++ tailWord_1740056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740056).length < 2 ^ (prefixWord ++ tailWord_1740056).sum := by decide
  have hdescent : baseEnd_1740056 < baseStart_1740056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740149 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 4]
def baseStart_1740149 : Nat := 118140960795 + 1740149 * 2 ^ 59
def prefixEnd_1740149 : Nat := 4983230072969 + 3 ^ 40 * 1740149 * 2
def baseEnd_1740149 : Nat := 397125709973696618993203

theorem tailTrace_1740149 : CollatzResearch.WordTrace tailWord_1740149 prefixEnd_1740149 397125709973696618993203 := by
  unfold tailWord_1740149
  simp only [CollatzResearch.WordTrace]
  refine ⟨63468448172744841633503501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42312298781829894422335667 63468448172744841633503501)
  ·
    refine ⟨23800668064779315612563813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63468448172744841633503501 23800668064779315612563813)
    ·
      refine ⟨4462625262146121677355715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23800668064779315612563813 4462625262146121677355715)
      ·
        refine ⟨6693937893219182516033573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4462625262146121677355715 6693937893219182516033573)
        ·
          refine ⟨1255113354978596721756295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6693937893219182516033573 1255113354978596721756295)
          ·
            refine ⟨1882670032467895082634443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255113354978596721756295 1882670032467895082634443)
            ·
              refine ⟨2824005048701842623951665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882670032467895082634443 2824005048701842623951665)
              ·
                refine ⟨2118003786526381967963749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824005048701842623951665 2118003786526381967963749)
                ·
                  refine ⟨397125709973696618993203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118003786526381967963749 397125709973696618993203)
                  ·
                    rfl

theorem cell21_1740149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_1740149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740149 prefixEnd_1740149 := by exact prefixLift 1740149
  have htrace : WordTrace (prefixWord ++ tailWord_1740149) baseStart_1740149 baseEnd_1740149 := by
    simpa [prefixWord, tailWord_1740149, baseEnd_1740149] using wordTrace_append hprefix tailTrace_1740149
  have hstable : (prefixWord ++ tailWord_1740149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740149).length < 2 ^ (prefixWord ++ tailWord_1740149).sum := by decide
  have hdescent : baseEnd_1740149 < baseStart_1740149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740194 : List Nat := [3, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_1740194 : Nat := 118140960795 + 1740194 * 2 ^ 59
def prefixEnd_1740194 : Nat := 4983230072969 + 3 ^ 40 * 1740194 * 2
def baseEnd_1740194 : Nat := 397135979586786540743111

theorem tailTrace_1740194 : CollatzResearch.WordTrace tailWord_1740194 prefixEnd_1740194 397135979586786540743111 := by
  unfold tailWord_1740194
  simp only [CollatzResearch.WordTrace]
  refine ⟨15867522364395453579722909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42313392971721209545927757 15867522364395453579722909)
  ·
    refine ⟨5950320886648295092396091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15867522364395453579722909 5950320886648295092396091)
    ·
      refine ⟨8925481329972442638594137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5950320886648295092396091 8925481329972442638594137)
      ·
        refine ⟨6694110997479331978945603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8925481329972442638594137 6694110997479331978945603)
        ·
          refine ⟨10041166496218997968418405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6694110997479331978945603 10041166496218997968418405)
          ·
            refine ⟨1882718718041062119078451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10041166496218997968418405 1882718718041062119078451)
            ·
              refine ⟨2824078077061593178617677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882718718041062119078451 2824078077061593178617677)
              ·
                refine ⟨1059029278898097441981629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2824078077061593178617677 1059029278898097441981629)
                ·
                  refine ⟨397135979586786540743111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059029278898097441981629 397135979586786540743111)
                  ·
                    rfl

theorem cell21_1740194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_1740194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740194 prefixEnd_1740194 := by exact prefixLift 1740194
  have htrace : WordTrace (prefixWord ++ tailWord_1740194) baseStart_1740194 baseEnd_1740194 := by
    simpa [prefixWord, tailWord_1740194, baseEnd_1740194] using wordTrace_append hprefix tailTrace_1740194
  have hstable : (prefixWord ++ tailWord_1740194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740194).length < 2 ^ (prefixWord ++ tailWord_1740194).sum := by decide
  have hdescent : baseEnd_1740194 < baseStart_1740194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740205 : List Nat := [1, 5, 2, 2, 1, 1, 9]
def baseStart_1740205 : Nat := 118140960795 + 1740205 * 2 ^ 59
def prefixEnd_1740205 : Nat := 4983230072969 + 3 ^ 40 * 1740205 * 2
def baseEnd_1740205 : Nat := 44126498881850329562195

theorem tailTrace_1740205 : CollatzResearch.WordTrace tailWord_1740205 prefixEnd_1740205 44126498881850329562195 := by
  unfold tailWord_1740205
  simp only [CollatzResearch.WordTrace]
  refine ⟨63470490660541963197542069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42313660440361308798361379 63470490660541963197542069)
  ·
    refine ⟨5950358499425809049769569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63470490660541963197542069 5950358499425809049769569)
    ·
      refine ⟨4462768874569356787327177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5950358499425809049769569 4462768874569356787327177)
      ·
        refine ⟨3347076655927017590495383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4462768874569356787327177 3347076655927017590495383)
        ·
          refine ⟨5020614983890526385743075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3347076655927017590495383 5020614983890526385743075)
          ·
            refine ⟨7530922475835789578614613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020614983890526385743075 7530922475835789578614613)
            ·
              refine ⟨44126498881850329562195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7530922475835789578614613 44126498881850329562195)
              ·
                rfl

theorem cell21_1740205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 9].length) (baseStart_1740205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740205 prefixEnd_1740205 := by exact prefixLift 1740205
  have htrace : WordTrace (prefixWord ++ tailWord_1740205) baseStart_1740205 baseEnd_1740205 := by
    simpa [prefixWord, tailWord_1740205, baseEnd_1740205] using wordTrace_append hprefix tailTrace_1740205
  have hstable : (prefixWord ++ tailWord_1740205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740205).length < 2 ^ (prefixWord ++ tailWord_1740205).sum := by decide
  have hdescent : baseEnd_1740205 < baseStart_1740205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740295 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 7]
def baseStart_1740295 : Nat := 118140960795 + 1740295 * 2 ^ 59
def prefixEnd_1740295 : Nat := 4983230072969 + 3 ^ 40 * 1740295 * 2
def baseEnd_1740295 : Nat := 397159029162832809559571

theorem tailTrace_1740295 : CollatzResearch.WordTrace tailWord_1740295 prefixEnd_1740295 397159029162832809559571 := by
  unfold tailWord_1740295
  simp only [CollatzResearch.WordTrace]
  refine ⟨63473773230215908568318339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42315848820143939045545559 63473773230215908568318339)
  ·
    refine ⟨95210659845323862852477509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63473773230215908568318339 95210659845323862852477509)
    ·
      refine ⟨17851998720998224284839533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95210659845323862852477509 17851998720998224284839533)
      ·
        refine ⟨6694499520374334106814825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17851998720998224284839533 6694499520374334106814825)
        ·
          refine ⟨5020874640280750580111119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6694499520374334106814825 5020874640280750580111119)
          ·
            refine ⟨7531311960421125870166679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020874640280750580111119 7531311960421125870166679)
            ·
              refine ⟨11296967940631688805250019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7531311960421125870166679 11296967940631688805250019)
              ·
                refine ⟨16945451910947533207875029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11296967940631688805250019 16945451910947533207875029)
                ·
                  refine ⟨397159029162832809559571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16945451910947533207875029 397159029162832809559571)
                  ·
                    rfl

theorem cell21_1740295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_1740295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740295 prefixEnd_1740295 := by exact prefixLift 1740295
  have htrace : WordTrace (prefixWord ++ tailWord_1740295) baseStart_1740295 baseEnd_1740295 := by
    simpa [prefixWord, tailWord_1740295, baseEnd_1740295] using wordTrace_append hprefix tailTrace_1740295
  have hstable : (prefixWord ++ tailWord_1740295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740295).length < 2 ^ (prefixWord ++ tailWord_1740295).sum := by decide
  have hdescent : baseEnd_1740295 < baseStart_1740295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740343 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 4]
def baseStart_1740343 : Nat := 118140960795 + 1740343 * 2 ^ 59
def prefixEnd_1740343 : Nat := 4983230072969 + 3 ^ 40 * 1740343 * 2
def baseEnd_1740343 : Nat := 397169983416795392759473

theorem tailTrace_1740343 : CollatzResearch.WordTrace tailWord_1740343 prefixEnd_1740343 397169983416795392759473 := by
  unfold tailWord_1740343
  simp only [CollatzResearch.WordTrace]
  refine ⟨63475523934042012766065683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42317015956028008510710455 63475523934042012766065683)
  ·
    refine ⟨95213285901063019149098525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63475523934042012766065683 95213285901063019149098525)
    ·
      refine ⟨35704982212898632180911947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95213285901063019149098525 35704982212898632180911947)
      ·
        refine ⟨53557473319347948271367921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35704982212898632180911947 53557473319347948271367921)
        ·
          refine ⟨40168104989510961203525941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53557473319347948271367921 40168104989510961203525941)
          ·
            refine ⟨3765759842766652612830557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40168104989510961203525941 3765759842766652612830557)
            ·
              refine ⟨1412159941037494729811459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3765759842766652612830557 1412159941037494729811459)
              ·
                refine ⟨2118239911556242094717189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412159941037494729811459 2118239911556242094717189)
                ·
                  refine ⟨397169983416795392759473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118239911556242094717189 397169983416795392759473)
                  ·
                    rfl

theorem cell21_1740343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 4].length) (baseStart_1740343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740343 prefixEnd_1740343 := by exact prefixLift 1740343
  have htrace : WordTrace (prefixWord ++ tailWord_1740343) baseStart_1740343 baseEnd_1740343 := by
    simpa [prefixWord, tailWord_1740343, baseEnd_1740343] using wordTrace_append hprefix tailTrace_1740343
  have hstable : (prefixWord ++ tailWord_1740343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740343).length < 2 ^ (prefixWord ++ tailWord_1740343).sum := by decide
  have hdescent : baseEnd_1740343 < baseStart_1740343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740385 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 6]
def baseStart_1740385 : Nat := 118140960795 + 1740385 * 2 ^ 59
def prefixEnd_1740385 : Nat := 4983230072969 + 3 ^ 40 * 1740385 * 2
def baseEnd_1740385 : Nat := 397179568389012653059387

theorem tailTrace_1740385 : CollatzResearch.WordTrace tailWord_1740385 prefixEnd_1740385 397179568389012653059387 := by
  unfold tailWord_1740385
  simp only [CollatzResearch.WordTrace]
  refine ⟨63477055799889853939094609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42318037199926569292729739 63477055799889853939094609)
  ·
    refine ⟨47607791849917390454320957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63477055799889853939094609 47607791849917390454320957)
    ·
      refine ⟨17852921943719021420370359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47607791849917390454320957 17852921943719021420370359)
      ·
        refine ⟨26779382915578532130555539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17852921943719021420370359 26779382915578532130555539)
        ·
          refine ⟨40169074373367798195833309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26779382915578532130555539 40169074373367798195833309)
          ·
            refine ⟨15063402890012924323437491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40169074373367798195833309 15063402890012924323437491)
            ·
              refine ⟨22595104335019386485156237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15063402890012924323437491 22595104335019386485156237)
              ·
                refine ⟨8473164125632269931933589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22595104335019386485156237 8473164125632269931933589)
                ·
                  refine ⟨397179568389012653059387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8473164125632269931933589 397179568389012653059387)
                  ·
                    rfl

theorem cell21_1740385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_1740385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740385 prefixEnd_1740385 := by exact prefixLift 1740385
  have htrace : WordTrace (prefixWord ++ tailWord_1740385) baseStart_1740385 baseEnd_1740385 := by
    simpa [prefixWord, tailWord_1740385, baseEnd_1740385] using wordTrace_append hprefix tailTrace_1740385
  have hstable : (prefixWord ++ tailWord_1740385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740385).length < 2 ^ (prefixWord ++ tailWord_1740385).sum := by decide
  have hdescent : baseEnd_1740385 < baseStart_1740385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740388 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_1740388 : Nat := 118140960795 + 1740388 * 2 ^ 59
def prefixEnd_1740388 : Nat := 4983230072969 + 3 ^ 40 * 1740388 * 2
def baseEnd_1740388 : Nat := 397180253029885314509381

theorem tailTrace_1740388 : CollatzResearch.WordTrace tailWord_1740388 prefixEnd_1740388 397180253029885314509381 := by
  unfold tailWord_1740388
  simp only [CollatzResearch.WordTrace]
  refine ⟨31738582609439492725726909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42318110145919323634302545 31738582609439492725726909)
  ·
    refine ⟨11901968478539809772147591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31738582609439492725726909 11901968478539809772147591)
    ·
      refine ⟨17852952717809714658221387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11901968478539809772147591 17852952717809714658221387)
      ·
        refine ⟨26779429076714571987332081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17852952717809714658221387 26779429076714571987332081)
        ·
          refine ⟨20084571807535928990499061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26779429076714571987332081 20084571807535928990499061)
          ·
            refine ⟨1882928606956493342859287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20084571807535928990499061 1882928606956493342859287)
            ·
              refine ⟨2824392910434740014288931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882928606956493342859287 2824392910434740014288931)
              ·
                refine ⟨4236589365652110021433397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824392910434740014288931 4236589365652110021433397)
                ·
                  refine ⟨397180253029885314509381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4236589365652110021433397 397180253029885314509381)
                  ·
                    rfl

theorem cell21_1740388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_1740388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740388 prefixEnd_1740388 := by exact prefixLift 1740388
  have htrace : WordTrace (prefixWord ++ tailWord_1740388) baseStart_1740388 baseEnd_1740388 := by
    simpa [prefixWord, tailWord_1740388, baseEnd_1740388] using wordTrace_append hprefix tailTrace_1740388
  have hstable : (prefixWord ++ tailWord_1740388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740388).length < 2 ^ (prefixWord ++ tailWord_1740388).sum := by decide
  have hdescent : baseEnd_1740388 < baseStart_1740388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740436 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1740436 : Nat := 118140960795 + 1740436 * 2 ^ 59
def prefixEnd_1740436 : Nat := 4983230072969 + 3 ^ 40 * 1740436 * 2
def baseEnd_1740436 : Nat := 397191207283847897709283

theorem tailTrace_1740436 : CollatzResearch.WordTrace tailWord_1740436 prefixEnd_1740436 397191207283847897709283 := by
  unfold tailWord_1740436
  simp only [CollatzResearch.WordTrace]
  refine ⟨31739457961352544824600581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42319277281803393099467441 31739457961352544824600581)
  ·
    refine ⟨5951148367753602154612609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31739457961352544824600581 5951148367753602154612609)
    ·
      refine ⟨4463361275815201615959457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5951148367753602154612609 4463361275815201615959457)
      ·
        refine ⟨3347520956861401211969593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4463361275815201615959457 3347520956861401211969593)
        ·
          refine ⟨2510640717646050908977195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3347520956861401211969593 2510640717646050908977195)
          ·
            refine ⟨3765961076469076363465793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510640717646050908977195 3765961076469076363465793)
            ·
              refine ⟨2824470807351807272599345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3765961076469076363465793 2824470807351807272599345)
              ·
                refine ⟨2118353105513855454449509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824470807351807272599345 2118353105513855454449509)
                ·
                  refine ⟨397191207283847897709283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118353105513855454449509 397191207283847897709283)
                  ·
                    rfl

theorem cell21_1740436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1740436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740436 prefixEnd_1740436 := by exact prefixLift 1740436
  have htrace : WordTrace (prefixWord ++ tailWord_1740436) baseStart_1740436 baseEnd_1740436 := by
    simpa [prefixWord, tailWord_1740436, baseEnd_1740436] using wordTrace_append hprefix tailTrace_1740436
  have hstable : (prefixWord ++ tailWord_1740436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740436).length < 2 ^ (prefixWord ++ tailWord_1740436).sum := by decide
  have hdescent : baseEnd_1740436 < baseStart_1740436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740475 : List Nat := [1, 1, 1, 1, 1, 2, 3, 11]
def baseStart_1740475 : Nat := 118140960795 + 1740475 * 2 ^ 59
def prefixEnd_1740475 : Nat := 4983230072969 + 3 ^ 40 * 1740475 * 2
def baseEnd_1740475 : Nat := 132400035871730832186401

theorem tailTrace_1740475 : CollatzResearch.WordTrace tailWord_1740475 prefixEnd_1740475 132400035871730832186401 := by
  unfold tailWord_1740475
  simp only [CollatzResearch.WordTrace]
  refine ⟨63480338369563799309870879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42320225579709199539913919 63480338369563799309870879)
  ·
    refine ⟨95220507554345698964806319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63480338369563799309870879 95220507554345698964806319)
    ·
      refine ⟨142830761331518548447209479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95220507554345698964806319 142830761331518548447209479)
      ·
        refine ⟨214246141997277822670814219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142830761331518548447209479 214246141997277822670814219)
        ·
          refine ⟨321369212995916734006221329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214246141997277822670814219 321369212995916734006221329)
          ·
            refine ⟨241026909746937550504665997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321369212995916734006221329 241026909746937550504665997)
            ·
              refine ⟨90385091155101581439249749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241026909746937550504665997 90385091155101581439249749)
              ·
                refine ⟨132400035871730832186401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 90385091155101581439249749 132400035871730832186401)
                ·
                  rfl

theorem cell21_1740475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 11].length) (baseStart_1740475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740475 prefixEnd_1740475 := by exact prefixLift 1740475
  have htrace : WordTrace (prefixWord ++ tailWord_1740475) baseStart_1740475 baseEnd_1740475 := by
    simpa [prefixWord, tailWord_1740475, baseEnd_1740475] using wordTrace_append hprefix tailTrace_1740475
  have hstable : (prefixWord ++ tailWord_1740475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740475).length < 2 ^ (prefixWord ++ tailWord_1740475).sum := by decide
  have hdescent : baseEnd_1740475 < baseStart_1740475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740616 : List Nat := [2, 1, 3, 1, 1, 5, 1, 4, 3]
def baseStart_1740616 : Nat := 118140960795 + 1740616 * 2 ^ 59
def prefixEnd_1740616 : Nat := 4983230072969 + 3 ^ 40 * 1740616 * 2
def baseEnd_1740616 : Nat := 397232285736207584708915

theorem tailTrace_1740616 : CollatzResearch.WordTrace tailWord_1740616 prefixEnd_1740616 397232285736207584708915 := by
  unfold tailWord_1740616
  simp only [CollatzResearch.WordTrace]
  refine ⟨31742740531026490195376851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42323654041368653593835801 31742740531026490195376851)
  ·
    refine ⟨47614110796539735293065277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31742740531026490195376851 47614110796539735293065277)
    ·
      refine ⟨17855291548702400734899479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47614110796539735293065277 17855291548702400734899479)
      ·
        refine ⟨26782937323053601102349219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17855291548702400734899479 26782937323053601102349219)
        ·
          refine ⟨40174405984580401653523829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26782937323053601102349219 40174405984580401653523829)
          ·
            refine ⟨3766350561054412655017859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40174405984580401653523829 3766350561054412655017859)
            ·
              refine ⟨5649525841581618982526789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766350561054412655017859 5649525841581618982526789)
              ·
                refine ⟨1059286095296553559223773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5649525841581618982526789 1059286095296553559223773)
                ·
                  refine ⟨397232285736207584708915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059286095296553559223773 397232285736207584708915)
                  ·
                    rfl

theorem cell21_1740616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_1740616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740616 prefixEnd_1740616 := by exact prefixLift 1740616
  have htrace : WordTrace (prefixWord ++ tailWord_1740616) baseStart_1740616 baseEnd_1740616 := by
    simpa [prefixWord, tailWord_1740616, baseEnd_1740616] using wordTrace_append hprefix tailTrace_1740616
  have hstable : (prefixWord ++ tailWord_1740616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740616).length < 2 ^ (prefixWord ++ tailWord_1740616).sum := by decide
  have hdescent : baseEnd_1740616 < baseStart_1740616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740650 : List Nat := [3, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_1740650 : Nat := 118140960795 + 1740650 * 2 ^ 59
def prefixEnd_1740650 : Nat := 4983230072969 + 3 ^ 40 * 1740650 * 2
def baseEnd_1740650 : Nat := 397240044999431081142179

theorem tailTrace_1740650 : CollatzResearch.WordTrace tailWord_1740650 prefixEnd_1740650 397240044999431081142179 := by
  unfold tailWord_1740650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871680285982451049372851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42324480762619869464994269 15871680285982451049372851)
  ·
    refine ⟨23807520428973676574059277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15871680285982451049372851 23807520428973676574059277)
    ·
      refine ⟨8927820160865128715272229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23807520428973676574059277 8927820160865128715272229)
      ·
        refine ⟨1673966280162211634113543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8927820160865128715272229 1673966280162211634113543)
        ·
          refine ⟨2510949420243317451170315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673966280162211634113543 2510949420243317451170315)
          ·
            refine ⟨3766424130364976176755473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510949420243317451170315 3766424130364976176755473)
            ·
              refine ⟨2824818097773732132566605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3766424130364976176755473 2824818097773732132566605)
              ·
                refine ⟨1059306786665149549712477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2824818097773732132566605 1059306786665149549712477)
                ·
                  refine ⟨397240044999431081142179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059306786665149549712477 397240044999431081142179)
                  ·
                    rfl

theorem cell21_1740650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_1740650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740650 prefixEnd_1740650 := by exact prefixLift 1740650
  have htrace : WordTrace (prefixWord ++ tailWord_1740650) baseStart_1740650 baseEnd_1740650 := by
    simpa [prefixWord, tailWord_1740650, baseEnd_1740650] using wordTrace_append hprefix tailTrace_1740650
  have hstable : (prefixWord ++ tailWord_1740650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740650).length < 2 ^ (prefixWord ++ tailWord_1740650).sum := by decide
  have hdescent : baseEnd_1740650 < baseStart_1740650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740658 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_1740658 : Nat := 118140960795 + 1740658 * 2 ^ 59
def prefixEnd_1740658 : Nat := 4983230072969 + 3 ^ 40 * 1740658 * 2
def baseEnd_1740658 : Nat := 397241870708424845008829

theorem tailTrace_1740658 : CollatzResearch.WordTrace tailWord_1740658 prefixEnd_1740658 397241870708424845008829 := by
  unfold tailWord_1740658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871753231975205390945657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42324675285267214375855085 15871753231975205390945657)
  ·
    refine ⟨11903814923981404043209243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15871753231975205390945657 11903814923981404043209243)
    ·
      refine ⟨17855722385972106064813865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11903814923981404043209243 17855722385972106064813865)
      ·
        refine ⟨13391791789479079548610399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17855722385972106064813865 13391791789479079548610399)
        ·
          refine ⟨20087687684218619322915599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13391791789479079548610399 20087687684218619322915599)
          ·
            refine ⟨30131531526327928984373399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20087687684218619322915599 30131531526327928984373399)
            ·
              refine ⟨45197297289491893476560099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30131531526327928984373399 45197297289491893476560099)
              ·
                refine ⟨67795945934237840214840149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45197297289491893476560099 67795945934237840214840149)
                ·
                  refine ⟨397241870708424845008829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67795945934237840214840149 397241870708424845008829)
                  ·
                    rfl

theorem cell21_1740658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_1740658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740658 prefixEnd_1740658 := by exact prefixLift 1740658
  have htrace : WordTrace (prefixWord ++ tailWord_1740658) baseStart_1740658 baseEnd_1740658 := by
    simpa [prefixWord, tailWord_1740658, baseEnd_1740658] using wordTrace_append hprefix tailTrace_1740658
  have hstable : (prefixWord ++ tailWord_1740658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740658).length < 2 ^ (prefixWord ++ tailWord_1740658).sum := by decide
  have hdescent : baseEnd_1740658 < baseStart_1740658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740675 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 5]
def baseStart_1740675 : Nat := 118140960795 + 1740675 * 2 ^ 59
def prefixEnd_1740675 : Nat := 4983230072969 + 3 ^ 40 * 1740675 * 2
def baseEnd_1740675 : Nat := 397245750340036593225461

theorem tailTrace_1740675 : CollatzResearch.WordTrace tailWord_1740675 prefixEnd_1740675 397245750340036593225461 := by
  unfold tailWord_1740675
  simp only [CollatzResearch.WordTrace]
  refine ⟨63487632968839233467151479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42325088645892822311434319 63487632968839233467151479)
  ·
    refine ⟨95231449453258850200727219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63487632968839233467151479 95231449453258850200727219)
    ·
      refine ⟨142847174179888275301090829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95231449453258850200727219 142847174179888275301090829)
      ·
        refine ⟨53567690317458103237909061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142847174179888275301090829 53567690317458103237909061)
        ·
          refine ⟨10043941934523394357107949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53567690317458103237909061 10043941934523394357107949)
          ·
            refine ⟨3766478225446272883915481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10043941934523394357107949 3766478225446272883915481)
            ·
              refine ⟨2824858669084704662936611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3766478225446272883915481 2824858669084704662936611)
              ·
                refine ⟨4237288003627056994404917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824858669084704662936611 4237288003627056994404917)
                ·
                  refine ⟨397245750340036593225461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4237288003627056994404917 397245750340036593225461)
                  ·
                    rfl

theorem cell21_1740675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 5].length) (baseStart_1740675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740675 prefixEnd_1740675 := by exact prefixLift 1740675
  have htrace : WordTrace (prefixWord ++ tailWord_1740675) baseStart_1740675 baseEnd_1740675 := by
    simpa [prefixWord, tailWord_1740675, baseEnd_1740675] using wordTrace_append hprefix tailTrace_1740675
  have hstable : (prefixWord ++ tailWord_1740675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740675).length < 2 ^ (prefixWord ++ tailWord_1740675).sum := by decide
  have hdescent : baseEnd_1740675 < baseStart_1740675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740689 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 4]
def baseStart_1740689 : Nat := 118140960795 + 1740689 * 2 ^ 59
def prefixEnd_1740689 : Nat := 4983230072969 + 3 ^ 40 * 1740689 * 2
def baseEnd_1740689 : Nat := 397248945330775679992099

theorem tailTrace_1740689 : CollatzResearch.WordTrace tailWord_1740689 prefixEnd_1740689 397248945330775679992099 := by
  unfold tailWord_1740689
  simp only [CollatzResearch.WordTrace]
  refine ⟨63488143590788513858161121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42325429060525675905440747 63488143590788513858161121)
  ·
    refine ⟨47616107693091385393620841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63488143590788513858161121 47616107693091385393620841)
    ·
      refine ⟨35712080769818539045215631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47616107693091385393620841 35712080769818539045215631)
      ·
        refine ⟨53568121154727808567823447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35712080769818539045215631 53568121154727808567823447)
        ·
          refine ⟨80352181732091712851735171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53568121154727808567823447 80352181732091712851735171)
          ·
            refine ⟨120528272598137569277602757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80352181732091712851735171 120528272598137569277602757)
            ·
              refine ⟨22599051112150794239550517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120528272598137569277602757 22599051112150794239550517)
              ·
                refine ⟨2118661041764136959957861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22599051112150794239550517 2118661041764136959957861)
                ·
                  refine ⟨397248945330775679992099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118661041764136959957861 397248945330775679992099)
                  ·
                    rfl

theorem cell21_1740689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_1740689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740689 prefixEnd_1740689 := by exact prefixLift 1740689
  have htrace : WordTrace (prefixWord ++ tailWord_1740689) baseStart_1740689 baseEnd_1740689 := by
    simpa [prefixWord, tailWord_1740689, baseEnd_1740689] using wordTrace_append hprefix tailTrace_1740689
  have hstable : (prefixWord ++ tailWord_1740689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740689).length < 2 ^ (prefixWord ++ tailWord_1740689).sum := by decide
  have hdescent : baseEnd_1740689 < baseStart_1740689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740782 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_1740782 : Nat := 118140960795 + 1740782 * 2 ^ 59
def prefixEnd_1740782 : Nat := 4983230072969 + 3 ^ 40 * 1740782 * 2
def baseEnd_1740782 : Nat := 397270169197828184941909

theorem tailTrace_1740782 : CollatzResearch.WordTrace tailWord_1740782 prefixEnd_1740782 397270169197828184941909 := by
  unfold tailWord_1740782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7936441947431448842662075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42327690386301060494197733 7936441947431448842662075)
  ·
    refine ⟨11904662921147173263993113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7936441947431448842662075 11904662921147173263993113)
    ·
      refine ⟨8928497190860379947994835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11904662921147173263993113 8928497190860379947994835)
      ·
        refine ⟨13392745786290569921992253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8928497190860379947994835 13392745786290569921992253)
        ·
          refine ⟨5022279669858963720747095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13392745786290569921992253 5022279669858963720747095)
          ·
            refine ⟨7533419504788445581120643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022279669858963720747095 7533419504788445581120643)
            ·
              refine ⟨11300129257182668371680965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7533419504788445581120643 11300129257182668371680965)
              ·
                refine ⟨2118774235721750319690181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11300129257182668371680965 2118774235721750319690181)
                ·
                  refine ⟨397270169197828184941909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118774235721750319690181 397270169197828184941909)
                  ·
                    rfl

theorem cell21_1740782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_1740782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740782 prefixEnd_1740782 := by exact prefixLift 1740782
  have htrace : WordTrace (prefixWord ++ tailWord_1740782) baseStart_1740782 baseEnd_1740782 := by
    simpa [prefixWord, tailWord_1740782, baseEnd_1740782] using wordTrace_append hprefix tailTrace_1740782
  have hstable : (prefixWord ++ tailWord_1740782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740782).length < 2 ^ (prefixWord ++ tailWord_1740782).sum := by decide
  have hdescent : baseEnd_1740782 < baseStart_1740782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740931 : List Nat := [1, 1, 1, 3, 3, 3, 2, 7]
def baseStart_1740931 : Nat := 118140960795 + 1740931 * 2 ^ 59
def prefixEnd_1740931 : Nat := 4983230072969 + 3 ^ 40 * 1740931 * 2
def baseEnd_1740931 : Nat := 132434724342612345652757

theorem tailTrace_1740931 : CollatzResearch.WordTrace tailWord_1740931 prefixEnd_1740931 132434724342612345652757 := by
  unfold tailWord_1740931
  simp only [CollatzResearch.WordTrace]
  refine ⟨63496970055911789188470647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42331313370607859458980431 63496970055911789188470647)
  ·
    refine ⟨95245455083867683782705971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63496970055911789188470647 95245455083867683782705971)
    ·
      refine ⟨142868182625801525674058957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95245455083867683782705971 142868182625801525674058957)
      ·
        refine ⟨53575568484675572127772109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142868182625801525674058957 53575568484675572127772109)
        ·
          refine ⟨20090838181753339547914541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53575568484675572127772109 20090838181753339547914541)
          ·
            refine ⟨7534064318157502330467953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20090838181753339547914541 7534064318157502330467953)
            ·
              refine ⟨5650548238618126747850965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7534064318157502330467953 5650548238618126747850965)
              ·
                refine ⟨132434724342612345652757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5650548238618126747850965 132434724342612345652757)
                ·
                  rfl

theorem cell21_1740931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 7].length) (baseStart_1740931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740931 prefixEnd_1740931 := by exact prefixLift 1740931
  have htrace : WordTrace (prefixWord ++ tailWord_1740931) baseStart_1740931 baseEnd_1740931 := by
    simpa [prefixWord, tailWord_1740931, baseEnd_1740931] using wordTrace_append hprefix tailTrace_1740931
  have hstable : (prefixWord ++ tailWord_1740931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740931).length < 2 ^ (prefixWord ++ tailWord_1740931).sum := by decide
  have hdescent : baseEnd_1740931 < baseStart_1740931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740948 : List Nat := [2, 4, 2, 3, 10]
def baseStart_1740948 : Nat := 118140960795 + 1740948 * 2 ^ 59
def prefixEnd_1740948 : Nat := 4983230072969 + 3 ^ 40 * 1740948 * 2
def baseEnd_1740948 : Nat := 4905037687153688705863

theorem tailTrace_1740948 : CollatzResearch.WordTrace tailWord_1740948 prefixEnd_1740948 4905037687153688705863 := by
  unfold tailWord_1740948
  simp only [CollatzResearch.WordTrace]
  refine ⟨31748795048425100545919749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42331726731233467394559665 31748795048425100545919749)
  ·
    refine ⟨5952899071579706352359953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31748795048425100545919749 5952899071579706352359953)
    ·
      refine ⟨4464674303684779764269965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5952899071579706352359953 4464674303684779764269965)
      ·
        refine ⟨1674252863881792411601237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4464674303684779764269965 1674252863881792411601237)
        ·
          refine ⟨4905037687153688705863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1674252863881792411601237 4905037687153688705863)
          ·
            rfl

theorem cell21_1740948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 10].length) (baseStart_1740948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740948 prefixEnd_1740948 := by exact prefixLift 1740948
  have htrace : WordTrace (prefixWord ++ tailWord_1740948) baseStart_1740948 baseEnd_1740948 := by
    simpa [prefixWord, tailWord_1740948, baseEnd_1740948] using wordTrace_append hprefix tailTrace_1740948
  have hstable : (prefixWord ++ tailWord_1740948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740948).length < 2 ^ (prefixWord ++ tailWord_1740948).sum := by decide
  have hdescent : baseEnd_1740948 < baseStart_1740948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740954 : List Nat := [3, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_1740954 : Nat := 118140960795 + 1740954 * 2 ^ 59
def prefixEnd_1740954 : Nat := 4983230072969 + 3 ^ 40 * 1740954 * 2
def baseEnd_1740954 : Nat := 397309421941194108074891

theorem tailTrace_1740954 : CollatzResearch.WordTrace tailWord_1740954 prefixEnd_1740954 397309421941194108074891 := by
  unfold tailWord_1740954
  simp only [CollatzResearch.WordTrace]
  refine ⟨15874452233707116029139479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42331872623218976077705277 15874452233707116029139479)
  ·
    refine ⟨23811678350560674043709219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15874452233707116029139479 23811678350560674043709219)
    ·
      refine ⟨35717517525841011065563829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23811678350560674043709219 35717517525841011065563829)
      ·
        refine ⟨3348517268047594787396609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35717517525841011065563829 3348517268047594787396609)
        ·
          refine ⟨2511387951035696090547457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3348517268047594787396609 2511387951035696090547457)
          ·
            refine ⟨1883540963276772067910593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2511387951035696090547457 1883540963276772067910593)
            ·
              refine ⟨1412655722457579050932945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883540963276772067910593 1412655722457579050932945)
              ·
                refine ⟨1059491791843184288199709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1412655722457579050932945 1059491791843184288199709)
                ·
                  refine ⟨397309421941194108074891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059491791843184288199709 397309421941194108074891)
                  ·
                    rfl

theorem cell21_1740954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_1740954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740954 prefixEnd_1740954 := by exact prefixLift 1740954
  have htrace : WordTrace (prefixWord ++ tailWord_1740954) baseStart_1740954 baseEnd_1740954 := by
    simpa [prefixWord, tailWord_1740954, baseEnd_1740954] using wordTrace_append hprefix tailTrace_1740954
  have hstable : (prefixWord ++ tailWord_1740954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740954).length < 2 ^ (prefixWord ++ tailWord_1740954).sum := by decide
  have hdescent : baseEnd_1740954 < baseStart_1740954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1740996 : List Nat := [2, 3, 3, 1, 2, 1, 1, 5, 3]
def baseStart_1740996 : Nat := 118140960795 + 1740996 * 2 ^ 59
def prefixEnd_1740996 : Nat := 4983230072969 + 3 ^ 40 * 1740996 * 2
def baseEnd_1740996 : Nat := 397319006913411368374805

theorem tailTrace_1740996 : CollatzResearch.WordTrace tailWord_1740996 prefixEnd_1740996 397319006913411368374805 := by
  unfold tailWord_1740996
  simp only [CollatzResearch.WordTrace]
  refine ⟨31749670400338152644793421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42332893867117536859724561 31749670400338152644793421)
  ·
    refine ⟨11906126400126807241797533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31749670400338152644793421 11906126400126807241797533)
    ·
      refine ⟨4464797400047552715674075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11906126400126807241797533 4464797400047552715674075)
      ·
        refine ⟨6697196100071329073511113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4464797400047552715674075 6697196100071329073511113)
        ·
          refine ⟨5022897075053496805133335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6697196100071329073511113 5022897075053496805133335)
          ·
            refine ⟨7534345612580245207700003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022897075053496805133335 7534345612580245207700003)
            ·
              refine ⟨11301518418870367811550005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7534345612580245207700003 11301518418870367811550005)
              ·
                refine ⟨1059517351769096982332813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11301518418870367811550005 1059517351769096982332813)
                ·
                  refine ⟨397319006913411368374805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059517351769096982332813 397319006913411368374805)
                  ·
                    rfl

theorem cell21_1740996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_1740996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1740996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1740996 prefixEnd_1740996 := by exact prefixLift 1740996
  have htrace : WordTrace (prefixWord ++ tailWord_1740996) baseStart_1740996 baseEnd_1740996 := by
    simpa [prefixWord, tailWord_1740996, baseEnd_1740996] using wordTrace_append hprefix tailTrace_1740996
  have hstable : (prefixWord ++ tailWord_1740996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1740996).length < 2 ^ (prefixWord ++ tailWord_1740996).sum := by decide
  have hdescent : baseEnd_1740996 < baseStart_1740996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1740996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741010 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_1741010 : Nat := 118140960795 + 1741010 * 2 ^ 59
def prefixEnd_1741010 : Nat := 4983230072969 + 3 ^ 40 * 1741010 * 2
def baseEnd_1741010 : Nat := 397322201904150455141443

theorem tailTrace_1741010 : CollatzResearch.WordTrace tailWord_1741010 prefixEnd_1741010 397322201904150455141443 := by
  unfold tailWord_1741010
  simp only [CollatzResearch.WordTrace]
  refine ⟨15874962855656396420149121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42333234281750390453730989 15874962855656396420149121)
  ·
    refine ⟨11906222141742297315111841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15874962855656396420149121 11906222141742297315111841)
    ·
      refine ⟨8929666606306722986333881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11906222141742297315111841 8929666606306722986333881)
      ·
        refine ⟨6697249954730042239750411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8929666606306722986333881 6697249954730042239750411)
        ·
          refine ⟨10045874932095063359625617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6697249954730042239750411 10045874932095063359625617)
          ·
            refine ⟨7534406199071297519719213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10045874932095063359625617 7534406199071297519719213)
            ·
              refine ⟨2825402324651736569894705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7534406199071297519719213 2825402324651736569894705)
              ·
                refine ⟨2119051743488802427421029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825402324651736569894705 2119051743488802427421029)
                ·
                  refine ⟨397322201904150455141443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2119051743488802427421029 397322201904150455141443)
                  ·
                    rfl

theorem cell21_1741010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_1741010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741010 prefixEnd_1741010 := by exact prefixLift 1741010
  have htrace : WordTrace (prefixWord ++ tailWord_1741010) baseStart_1741010 baseEnd_1741010 := by
    simpa [prefixWord, tailWord_1741010, baseEnd_1741010] using wordTrace_append hprefix tailTrace_1741010
  have hstable : (prefixWord ++ tailWord_1741010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741010).length < 2 ^ (prefixWord ++ tailWord_1741010).sum := by decide
  have hdescent : baseEnd_1741010 < baseStart_1741010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741128 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_1741128 : Nat := 118140960795 + 1741128 * 2 ^ 59
def prefixEnd_1741128 : Nat := 4983230072969 + 3 ^ 40 * 1741128 * 2
def baseEnd_1741128 : Nat := 397349131111808472174535

theorem tailTrace_1741128 : CollatzResearch.WordTrace tailWord_1741128 prefixEnd_1741128 397349131111808472174535 := by
  unfold tailWord_1741128
  simp only [CollatzResearch.WordTrace]
  refine ⟨31752077618099045916696019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42336103490798727888928025 31752077618099045916696019)
  ·
    refine ⟨47628116427148568875044029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31752077618099045916696019 47628116427148568875044029)
    ·
      refine ⟨17860543660180713328141511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47628116427148568875044029 17860543660180713328141511)
      ·
        refine ⟨26790815490271069992212267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17860543660180713328141511 26790815490271069992212267)
        ·
          refine ⟨40186223235406604988318401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26790815490271069992212267 40186223235406604988318401)
          ·
            refine ⟨30139667426554953741238801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40186223235406604988318401 30139667426554953741238801)
            ·
              refine ⟨22604750569916215305929101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30139667426554953741238801 22604750569916215305929101)
              ·
                refine ⟨8476781463718580739723413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22604750569916215305929101 8476781463718580739723413)
                ·
                  refine ⟨397349131111808472174535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8476781463718580739723413 397349131111808472174535)
                  ·
                    rfl

theorem cell21_1741128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_1741128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741128 prefixEnd_1741128 := by exact prefixLift 1741128
  have htrace : WordTrace (prefixWord ++ tailWord_1741128) baseStart_1741128 baseEnd_1741128 := by
    simpa [prefixWord, tailWord_1741128, baseEnd_1741128] using wordTrace_append hprefix tailTrace_1741128
  have hstable : (prefixWord ++ tailWord_1741128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741128).length < 2 ^ (prefixWord ++ tailWord_1741128).sum := by decide
  have hdescent : baseEnd_1741128 < baseStart_1741128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741148 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_1741148 : Nat := 118140960795 + 1741148 * 2 ^ 59
def prefixEnd_1741148 : Nat := 4983230072969 + 3 ^ 40 * 1741148 * 2
def baseEnd_1741148 : Nat := 397353695384292881841161

theorem tailTrace_1741148 : CollatzResearch.WordTrace tailWord_1741148 prefixEnd_1741148 397353695384292881841161 := by
  unfold tailWord_1741148
  simp only [CollatzResearch.WordTrace]
  refine ⟨31752442348062817624560049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42336589797417090166080065 31752442348062817624560049)
  ·
    refine ⟨23814331761047113218420037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31752442348062817624560049 23814331761047113218420037)
    ·
      refine ⟨4465187205196333728453757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23814331761047113218420037 4465187205196333728453757)
      ·
        refine ⟨1674445201948625148170159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4465187205196333728453757 1674445201948625148170159)
        ·
          refine ⟨2511667802922937722255239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674445201948625148170159 2511667802922937722255239)
          ·
            refine ⟨3767501704384406583382859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511667802922937722255239 3767501704384406583382859)
            ·
              refine ⟨5651252556576609875074289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3767501704384406583382859 5651252556576609875074289)
              ·
                refine ⟨4238439417432457406305717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5651252556576609875074289 4238439417432457406305717)
                ·
                  refine ⟨397353695384292881841161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4238439417432457406305717 397353695384292881841161)
                  ·
                    rfl

theorem cell21_1741148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_1741148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741148 prefixEnd_1741148 := by exact prefixLift 1741148
  have htrace : WordTrace (prefixWord ++ tailWord_1741148) baseStart_1741148 baseEnd_1741148 := by
    simpa [prefixWord, tailWord_1741148, baseEnd_1741148] using wordTrace_append hprefix tailTrace_1741148
  have hstable : (prefixWord ++ tailWord_1741148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741148).length < 2 ^ (prefixWord ++ tailWord_1741148).sum := by decide
  have hdescent : baseEnd_1741148 < baseStart_1741148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741297 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 4]
def baseStart_1741297 : Nat := 118140960795 + 1741297 * 2 ^ 59
def prefixEnd_1741297 : Nat := 4983230072969 + 3 ^ 40 * 1741297 * 2
def baseEnd_1741297 : Nat := 397387699214301733857523

theorem tailTrace_1741297 : CollatzResearch.WordTrace tailWord_1741297 prefixEnd_1741297 397387699214301733857523 := by
  unfold tailWord_1741297
  simp only [CollatzResearch.WordTrace]
  refine ⟨63510319172585833696294145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42340212781723889130862763 63510319172585833696294145)
  ·
    refine ⟨47632739379439375272220609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63510319172585833696294145 47632739379439375272220609)
    ·
      refine ⟨35724554534579531454165457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47632739379439375272220609 35724554534579531454165457)
      ·
        refine ⟨26793415900934648590624093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35724554534579531454165457 26793415900934648590624093)
        ·
          refine ⟨10047530962850493221484035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26793415900934648590624093 10047530962850493221484035)
          ·
            refine ⟨15071296444275739832226053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10047530962850493221484035 15071296444275739832226053)
            ·
              refine ⟨2825868083301701218542385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15071296444275739832226053 2825868083301701218542385)
              ·
                refine ⟨2119401062476275913906789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825868083301701218542385 2119401062476275913906789)
                ·
                  refine ⟨397387699214301733857523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2119401062476275913906789 397387699214301733857523)
                  ·
                    rfl

theorem cell21_1741297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_1741297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741297 prefixEnd_1741297 := by exact prefixLift 1741297
  have htrace : WordTrace (prefixWord ++ tailWord_1741297) baseStart_1741297 baseEnd_1741297 := by
    simpa [prefixWord, tailWord_1741297, baseEnd_1741297] using wordTrace_append hprefix tailTrace_1741297
  have hstable : (prefixWord ++ tailWord_1741297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741297).length < 2 ^ (prefixWord ++ tailWord_1741297).sum := by decide
  have hdescent : baseEnd_1741297 < baseStart_1741297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741348 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 4]
def baseStart_1741348 : Nat := 118140960795 + 1741348 * 2 ^ 59
def prefixEnd_1741348 : Nat := 4983230072969 + 3 ^ 40 * 1741348 * 2
def baseEnd_1741348 : Nat := 397399338109136978507419

theorem tailTrace_1741348 : CollatzResearch.WordTrace tailWord_1741348 prefixEnd_1741348 397399338109136978507419 := by
  unfold tailWord_1741348
  simp only [CollatzResearch.WordTrace]
  refine ⟨31756089647700534703200349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42341452863600712937600465 31756089647700534703200349)
  ·
    refine ⟨11908533617887700513700131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31756089647700534703200349 11908533617887700513700131)
    ·
      refine ⟨17862800426831550770550197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11908533617887700513700131 17862800426831550770550197)
      ·
        refine ⟨1674637540015457884739081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17862800426831550770550197 1674637540015457884739081)
        ·
          refine ⟨1255978155011593413554311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1674637540015457884739081 1255978155011593413554311)
          ·
            refine ⟨1883967232517390120331467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255978155011593413554311 1883967232517390120331467)
            ·
              refine ⟨2825950848776085180497201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883967232517390120331467 2825950848776085180497201)
              ·
                refine ⟨2119463136582063885372901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825950848776085180497201 2119463136582063885372901)
                ·
                  refine ⟨397399338109136978507419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2119463136582063885372901 397399338109136978507419)
                  ·
                    rfl

theorem cell21_1741348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_1741348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741348 prefixEnd_1741348 := by exact prefixLift 1741348
  have htrace : WordTrace (prefixWord ++ tailWord_1741348) baseStart_1741348 baseEnd_1741348 := by
    simpa [prefixWord, tailWord_1741348, baseEnd_1741348] using wordTrace_append hprefix tailTrace_1741348
  have hstable : (prefixWord ++ tailWord_1741348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741348).length < 2 ^ (prefixWord ++ tailWord_1741348).sum := by decide
  have hdescent : baseEnd_1741348 < baseStart_1741348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741387 : List Nat := [1, 1, 1, 1, 3, 1, 8, 5]
def baseStart_1741387 : Nat := 118140960795 + 1741387 * 2 ^ 59
def prefixEnd_1741387 : Nat := 4983230072969 + 3 ^ 40 * 1741387 * 2
def baseEnd_1741387 : Nat := 132469412813493859119113

theorem tailTrace_1741387 : CollatzResearch.WordTrace tailWord_1741387 prefixEnd_1741387 132469412813493859119113 := by
  unfold tailWord_1741387
  simp only [CollatzResearch.WordTrace]
  refine ⟨63513601742259779067070415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42342401161506519378046943 63513601742259779067070415)
  ·
    refine ⟨95270402613389668600605623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63513601742259779067070415 95270402613389668600605623)
    ·
      refine ⟨142905603920084502900908435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95270402613389668600605623 142905603920084502900908435)
      ·
        refine ⟨214358405880126754351362653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142905603920084502900908435 214358405880126754351362653)
        ·
          refine ⟨80384402205047532881760995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214358405880126754351362653 80384402205047532881760995)
          ·
            refine ⟨120576603307571299322641493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80384402205047532881760995 120576603307571299322641493)
            ·
              refine ⟨1413007070010601163937205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 120576603307571299322641493 1413007070010601163937205)
              ·
                refine ⟨132469412813493859119113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1413007070010601163937205 132469412813493859119113)
                ·
                  rfl

theorem cell21_1741387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 5].length) (baseStart_1741387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741387 prefixEnd_1741387 := by exact prefixLift 1741387
  have htrace : WordTrace (prefixWord ++ tailWord_1741387) baseStart_1741387 baseEnd_1741387 := by
    simpa [prefixWord, tailWord_1741387, baseEnd_1741387] using wordTrace_append hprefix tailTrace_1741387
  have hstable : (prefixWord ++ tailWord_1741387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741387).length < 2 ^ (prefixWord ++ tailWord_1741387).sum := by decide
  have hdescent : baseEnd_1741387 < baseStart_1741387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741404 : List Nat := [2, 2, 4, 1, 3, 2, 7]
def baseStart_1741404 : Nat := 118140960795 + 1741404 * 2 ^ 59
def prefixEnd_1741404 : Nat := 4983230072969 + 3 ^ 40 * 1741404 * 2
def baseEnd_1741404 : Nat := 44156902008010369508219

theorem tailTrace_1741404 : CollatzResearch.WordTrace tailWord_1741404 prefixEnd_1741404 44156902008010369508219 := by
  unfold tailWord_1741404
  simp only [CollatzResearch.WordTrace]
  refine ⟨31757110891599095485219633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42342814522132127313626177 31757110891599095485219633)
  ·
    refine ⟨23817833168699321613914725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31757110891599095485219633 23817833168699321613914725)
    ·
      refine ⟨4465843719131122802609011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23817833168699321613914725 4465843719131122802609011)
      ·
        refine ⟨6698765578696684203913517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465843719131122802609011 6698765578696684203913517)
        ·
          refine ⟨2512037092011256576467569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6698765578696684203913517 2512037092011256576467569)
          ·
            refine ⟨1884027819008442432350677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2512037092011256576467569 1884027819008442432350677)
            ·
              refine ⟨44156902008010369508219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1884027819008442432350677 44156902008010369508219)
              ·
                rfl

theorem cell21_1741404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 7].length) (baseStart_1741404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741404 prefixEnd_1741404 := by exact prefixLift 1741404
  have htrace : WordTrace (prefixWord ++ tailWord_1741404) baseStart_1741404 baseEnd_1741404 := by
    simpa [prefixWord, tailWord_1741404, baseEnd_1741404] using wordTrace_append hprefix tailTrace_1741404
  have hstable : (prefixWord ++ tailWord_1741404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741404).length < 2 ^ (prefixWord ++ tailWord_1741404).sum := by decide
  have hdescent : baseEnd_1741404 < baseStart_1741404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741410 : List Nat := [3, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_1741410 : Nat := 118140960795 + 1741410 * 2 ^ 59
def prefixEnd_1741410 : Nat := 4983230072969 + 3 ^ 40 * 1741410 * 2
def baseEnd_1741410 : Nat := 397413487353838648473959

theorem tailTrace_1741410 : CollatzResearch.WordTrace tailWord_1741410 prefixEnd_1741410 397413487353838648473959 := by
  unfold tailWord_1741410
  simp only [CollatzResearch.WordTrace]
  refine ⟨15878610155294113498789421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42342960414117635996771789 15878610155294113498789421)
  ·
    refine ⟨5954478808235292562046033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15878610155294113498789421 5954478808235292562046033)
    ·
      refine ⟨4465859106176469421534525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5954478808235292562046033 4465859106176469421534525)
      ·
        refine ⟨1674697164816176033075447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4465859106176469421534525 1674697164816176033075447)
        ·
          refine ⟨2512045747224264049613171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674697164816176033075447 2512045747224264049613171)
          ·
            refine ⟨3768068620836396074419757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512045747224264049613171 3768068620836396074419757)
            ·
              refine ⟨1413025732813648527907409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3768068620836396074419757 1413025732813648527907409)
              ·
                refine ⟨1059769299610236395930557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413025732813648527907409 1059769299610236395930557)
                ·
                  refine ⟨397413487353838648473959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059769299610236395930557 397413487353838648473959)
                  ·
                    rfl

theorem cell21_1741410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_1741410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741410 prefixEnd_1741410 := by exact prefixLift 1741410
  have htrace : WordTrace (prefixWord ++ tailWord_1741410) baseStart_1741410 baseEnd_1741410 := by
    simpa [prefixWord, tailWord_1741410, baseEnd_1741410] using wordTrace_append hprefix tailTrace_1741410
  have hstable : (prefixWord ++ tailWord_1741410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741410).length < 2 ^ (prefixWord ++ tailWord_1741410).sum := by decide
  have hdescent : baseEnd_1741410 < baseStart_1741410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741432 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_1741432 : Nat := 118140960795 + 1741432 * 2 ^ 59
def prefixEnd_1741432 : Nat := 4983230072969 + 3 ^ 40 * 1741432 * 2
def baseEnd_1741432 : Nat := 397418508053571499107247

theorem tailTrace_1741432 : CollatzResearch.WordTrace tailWord_1741432 prefixEnd_1741432 397418508053571499107247 := by
  unfold tailWord_1741432
  simp only [CollatzResearch.WordTrace]
  refine ⟨31757621513548375876229275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42343495351397834501639033 31757621513548375876229275)
  ·
    refine ⟨47636432270322563814343913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31757621513548375876229275 47636432270322563814343913)
    ·
      refine ⟨35727324202741922860757935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47636432270322563814343913 35727324202741922860757935)
      ·
        refine ⟨53590986304112884291136903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35727324202741922860757935 53590986304112884291136903)
        ·
          refine ⟨80386479456169326436705355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53590986304112884291136903 80386479456169326436705355)
          ·
            refine ⟨120579719184253989655058033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80386479456169326436705355 120579719184253989655058033)
            ·
              refine ⟨90434789388190492241293525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120579719184253989655058033 90434789388190492241293525)
              ·
                refine ⟨2119565376285714661905317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90434789388190492241293525 2119565376285714661905317)
                ·
                  refine ⟨397418508053571499107247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2119565376285714661905317 397418508053571499107247)
                  ·
                    rfl

theorem cell21_1741432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_1741432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741432 prefixEnd_1741432 := by exact prefixLift 1741432
  have htrace : WordTrace (prefixWord ++ tailWord_1741432) baseStart_1741432 baseEnd_1741432 := by
    simpa [prefixWord, tailWord_1741432, baseEnd_1741432] using wordTrace_append hprefix tailTrace_1741432
  have hstable : (prefixWord ++ tailWord_1741432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741432).length < 2 ^ (prefixWord ++ tailWord_1741432).sum := by decide
  have hdescent : baseEnd_1741432 < baseStart_1741432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741477 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 5]
def baseStart_1741477 : Nat := 118140960795 + 1741477 * 2 ^ 59
def prefixEnd_1741477 : Nat := 4983230072969 + 3 ^ 40 * 1741477 * 2
def baseEnd_1741477 : Nat := 397428777666661420857155

theorem tailTrace_1741477 : CollatzResearch.WordTrace tailWord_1741477 prefixEnd_1741477 397428777666661420857155 := by
  unfold tailWord_1741477
  simp only [CollatzResearch.WordTrace]
  refine ⟨63516884311933724437846685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42344589541289149625231123 63516884311933724437846685)
  ·
    refine ⟨23818831616975146664192507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63516884311933724437846685 23818831616975146664192507)
    ·
      refine ⟨35728247425462719996288761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23818831616975146664192507 35728247425462719996288761)
      ·
        refine ⟨26796185569097039997216571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35728247425462719996288761 26796185569097039997216571)
        ·
          refine ⟨40194278353645559995824857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26796185569097039997216571 40194278353645559995824857)
          ·
            refine ⟨30145708765234169996868643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40194278353645559995824857 30145708765234169996868643)
            ·
              refine ⟨45218563147851254995302965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30145708765234169996868643 45218563147851254995302965)
              ·
                refine ⟨4239240295111055155809653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45218563147851254995302965 4239240295111055155809653)
                ·
                  refine ⟨397428777666661420857155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4239240295111055155809653 397428777666661420857155)
                  ·
                    rfl

theorem cell21_1741477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_1741477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741477 prefixEnd_1741477 := by exact prefixLift 1741477
  have htrace : WordTrace (prefixWord ++ tailWord_1741477) baseStart_1741477 baseEnd_1741477 := by
    simpa [prefixWord, tailWord_1741477, baseEnd_1741477] using wordTrace_append hprefix tailTrace_1741477
  have hstable : (prefixWord ++ tailWord_1741477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741477).length < 2 ^ (prefixWord ++ tailWord_1741477).sum := by decide
  have hdescent : baseEnd_1741477 < baseStart_1741477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741553 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 5]
def baseStart_1741553 : Nat := 118140960795 + 1741553 * 2 ^ 59
def prefixEnd_1741553 : Nat := 4983230072969 + 3 ^ 40 * 1741553 * 2
def baseEnd_1741553 : Nat := 397446121902102177590333

theorem tailTrace_1741553 : CollatzResearch.WordTrace tailWord_1741553 prefixEnd_1741553 397446121902102177590333 := by
  unfold tailWord_1741553
  simp only [CollatzResearch.WordTrace]
  refine ⟨63519656259658389417613313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42346437506438926278408875 63519656259658389417613313)
  ·
    refine ⟨47639742194743792063209985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63519656259658389417613313 47639742194743792063209985)
    ·
      refine ⟨35729806646057844047407489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47639742194743792063209985 35729806646057844047407489)
      ·
        refine ⟨26797354984543383035555617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35729806646057844047407489 26797354984543383035555617)
        ·
          refine ⟨20098016238407537276666713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26797354984543383035555617 20098016238407537276666713)
          ·
            refine ⟨15073512178805652957500035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20098016238407537276666713 15073512178805652957500035)
            ·
              refine ⟨22610268268208479436250053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15073512178805652957500035 22610268268208479436250053)
              ·
                refine ⟨4239425300289089894296885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22610268268208479436250053 4239425300289089894296885)
                ·
                  refine ⟨397446121902102177590333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4239425300289089894296885 397446121902102177590333)
                  ·
                    rfl

theorem cell21_1741553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_1741553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741553 prefixEnd_1741553 := by exact prefixLift 1741553
  have htrace : WordTrace (prefixWord ++ tailWord_1741553) baseStart_1741553 baseEnd_1741553 := by
    simpa [prefixWord, tailWord_1741553, baseEnd_1741553] using wordTrace_append hprefix tailTrace_1741553
  have hstable : (prefixWord ++ tailWord_1741553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741553).length < 2 ^ (prefixWord ++ tailWord_1741553).sum := by decide
  have hdescent : baseEnd_1741553 < baseStart_1741553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741587 : List Nat := [1, 1, 1, 2, 1, 3, 7, 2, 3]
def baseStart_1741587 : Nat := 118140960795 + 1741587 * 2 ^ 59
def prefixEnd_1741587 : Nat := 4983230072969 + 3 ^ 40 * 1741587 * 2
def baseEnd_1741587 : Nat := 397453881165325674023597

theorem tailTrace_1741587 : CollatzResearch.WordTrace tailWord_1741587 prefixEnd_1741587 397453881165325674023597 := by
  unfold tailWord_1741587
  simp only [CollatzResearch.WordTrace]
  refine ⟨63520896341535213224351015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42347264227690142149567343 63520896341535213224351015)
  ·
    refine ⟨95281344512302819836526523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63520896341535213224351015 95281344512302819836526523)
    ·
      refine ⟨142922016768454229754789785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95281344512302819836526523 142922016768454229754789785)
      ·
        refine ⟨107191512576340672316092339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142922016768454229754789785 107191512576340672316092339)
        ·
          refine ⟨160787268864511008474138509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107191512576340672316092339 160787268864511008474138509)
          ·
            refine ⟨60295225824191628177801941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160787268864511008474138509 60295225824191628177801941)
            ·
              refine ⟨1413169355254491285417233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 60295225824191628177801941 1413169355254491285417233)
              ·
                refine ⟨1059877016440868464062925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413169355254491285417233 1059877016440868464062925)
                ·
                  refine ⟨397453881165325674023597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059877016440868464062925 397453881165325674023597)
                  ·
                    rfl

theorem cell21_1741587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 3].length) (baseStart_1741587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741587 prefixEnd_1741587 := by exact prefixLift 1741587
  have htrace : WordTrace (prefixWord ++ tailWord_1741587) baseStart_1741587 baseEnd_1741587 := by
    simpa [prefixWord, tailWord_1741587, baseEnd_1741587] using wordTrace_append hprefix tailTrace_1741587
  have hstable : (prefixWord ++ tailWord_1741587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741587).length < 2 ^ (prefixWord ++ tailWord_1741587).sum := by decide
  have hdescent : baseEnd_1741587 < baseStart_1741587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741694 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1741694 : Nat := 118140960795 + 1741694 * 2 ^ 59
def prefixEnd_1741694 : Nat := 4983230072969 + 3 ^ 40 * 1741694 * 2
def baseEnd_1741694 : Nat := 397478300023117265740045

theorem tailTrace_1741694 : CollatzResearch.WordTrace tailWord_1741694 prefixEnd_1741694 397478300023117265740045 := by
  unfold tailWord_1741694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7940599869018446312312017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42349865968098380332330757 7940599869018446312312017)
  ·
    refine ⟨5955449901763834734234013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7940599869018446312312017 5955449901763834734234013)
    ·
      refine ⟨2233293713161438025337755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5955449901763834734234013 2233293713161438025337755)
      ·
        refine ⟨3349940569742157038006633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233293713161438025337755 3349940569742157038006633)
        ·
          refine ⟨2512455427306617778504975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3349940569742157038006633 2512455427306617778504975)
          ·
            refine ⟨3768683140959926667757463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512455427306617778504975 3768683140959926667757463)
            ·
              refine ⟨5653024711439890001636195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3768683140959926667757463 5653024711439890001636195)
              ·
                refine ⟨8479537067159835002454293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5653024711439890001636195 8479537067159835002454293)
                ·
                  refine ⟨397478300023117265740045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8479537067159835002454293 397478300023117265740045)
                  ·
                    rfl

theorem cell21_1741694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1741694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741694 prefixEnd_1741694 := by exact prefixLift 1741694
  have htrace : WordTrace (prefixWord ++ tailWord_1741694) baseStart_1741694 baseEnd_1741694 := by
    simpa [prefixWord, tailWord_1741694, baseEnd_1741694] using wordTrace_append hprefix tailTrace_1741694
  have hstable : (prefixWord ++ tailWord_1741694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741694).length < 2 ^ (prefixWord ++ tailWord_1741694).sum := by decide
  have hdescent : baseEnd_1741694 < baseStart_1741694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741705 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 5]
def baseStart_1741705 : Nat := 118140960795 + 1741705 * 2 ^ 59
def prefixEnd_1741705 : Nat := 4983230072969 + 3 ^ 40 * 1741705 * 2
def baseEnd_1741705 : Nat := 397480810372983691056689

theorem tailTrace_1741705 : CollatzResearch.WordTrace tailWord_1741705 prefixEnd_1741705 397480810372983691056689 := by
  unfold tailWord_1741705
  simp only [CollatzResearch.WordTrace]
  refine ⟨63525200155107719377146569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42350133436738479584764379 63525200155107719377146569)
  ·
    refine ⟨47643900116330789532859927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63525200155107719377146569 47643900116330789532859927)
    ·
      refine ⟨71465850174496184299289891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47643900116330789532859927 71465850174496184299289891)
      ·
        refine ⟨107198775261744276448934837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71465850174496184299289891 107198775261744276448934837)
        ·
          refine ⟨10049885180788525917087641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107198775261744276448934837 10049885180788525917087641)
          ·
            refine ⟨7537413885591394437815731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10049885180788525917087641 7537413885591394437815731)
            ·
              refine ⟨11306120828387091656723597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7537413885591394437815731 11306120828387091656723597)
              ·
                refine ⟨4239795310645159371271349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11306120828387091656723597 4239795310645159371271349)
                ·
                  refine ⟨397480810372983691056689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4239795310645159371271349 397480810372983691056689)
                  ·
                    rfl

theorem cell21_1741705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_1741705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741705 prefixEnd_1741705 := by exact prefixLift 1741705
  have htrace : WordTrace (prefixWord ++ tailWord_1741705) baseStart_1741705 baseEnd_1741705 := by
    simpa [prefixWord, tailWord_1741705, baseEnd_1741705] using wordTrace_append hprefix tailTrace_1741705
  have hstable : (prefixWord ++ tailWord_1741705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741705).length < 2 ^ (prefixWord ++ tailWord_1741705).sum := by decide
  have hdescent : baseEnd_1741705 < baseStart_1741705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741874 : List Nat := [3, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_1741874 : Nat := 118140960795 + 1741874 * 2 ^ 59
def prefixEnd_1741874 : Nat := 4983230072969 + 3 ^ 40 * 1741874 * 2
def baseEnd_1741874 : Nat := 397519378475476952739677

theorem tailTrace_1741874 : CollatzResearch.WordTrace tailWord_1741874 prefixEnd_1741874 397519378475476952739677 := by
  unfold tailWord_1741874
  simp only [CollatzResearch.WordTrace]
  refine ⟨15882841022873865310012169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42354242727663640826699117 15882841022873865310012169)
  ·
    refine ⟨11912130767155398982509127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15882841022873865310012169 11912130767155398982509127)
    ·
      refine ⟨17868196150733098473763691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11912130767155398982509127 17868196150733098473763691)
      ·
        refine ⟨26802294226099647710645537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17868196150733098473763691 26802294226099647710645537)
        ·
          refine ⟨20101720669574735782984153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26802294226099647710645537 20101720669574735782984153)
          ·
            refine ⟨15076290502181051837238115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20101720669574735782984153 15076290502181051837238115)
            ·
              refine ⟨22614435753271577755857173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15076290502181051837238115 22614435753271577755857173)
              ·
                refine ⟨1060051675934605207305805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22614435753271577755857173 1060051675934605207305805)
                ·
                  refine ⟨397519378475476952739677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1060051675934605207305805 397519378475476952739677)
                  ·
                    rfl

theorem cell21_1741874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_1741874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741874 prefixEnd_1741874 := by exact prefixLift 1741874
  have htrace : WordTrace (prefixWord ++ tailWord_1741874) baseStart_1741874 baseEnd_1741874 := by
    simpa [prefixWord, tailWord_1741874, baseEnd_1741874] using wordTrace_append hprefix tailTrace_1741874
  have hstable : (prefixWord ++ tailWord_1741874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741874).length < 2 ^ (prefixWord ++ tailWord_1741874).sum := by decide
  have hdescent : baseEnd_1741874 < baseStart_1741874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741902 : List Nat := [4, 1, 1, 1, 1, 3, 3, 7]
def baseStart_1741902 : Nat := 118140960795 + 1741902 * 2 ^ 59
def prefixEnd_1741902 : Nat := 4983230072969 + 3 ^ 40 * 1741902 * 2
def baseEnd_1741902 : Nat := 132508589485651708757651

theorem tailTrace_1741902 : CollatzResearch.WordTrace tailWord_1741902 prefixEnd_1741902 132508589485651708757651 := by
  unfold tailWord_1741902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941548166924252752758495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42354923556929348014711973 7941548166924252752758495)
  ·
    refine ⟨11912322250386379129137743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7941548166924252752758495 11912322250386379129137743)
    ·
      refine ⟨17868483375579568693706615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11912322250386379129137743 17868483375579568693706615)
      ·
        refine ⟨26802725063369353040559923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17868483375579568693706615 26802725063369353040559923)
        ·
          refine ⟨40204087595054029560839885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26802725063369353040559923 40204087595054029560839885)
          ·
            refine ⟨15076532848145261085314957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40204087595054029560839885 15076532848145261085314957)
            ·
              refine ⟨5653699818054472906993109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15076532848145261085314957 5653699818054472906993109)
              ·
                refine ⟨132508589485651708757651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5653699818054472906993109 132508589485651708757651)
                ·
                  rfl

theorem cell21_1741902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_1741902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741902 prefixEnd_1741902 := by exact prefixLift 1741902
  have htrace : WordTrace (prefixWord ++ tailWord_1741902) baseStart_1741902 baseEnd_1741902 := by
    simpa [prefixWord, tailWord_1741902, baseEnd_1741902] using wordTrace_append hprefix tailTrace_1741902
  have hstable : (prefixWord ++ tailWord_1741902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741902).length < 2 ^ (prefixWord ++ tailWord_1741902).sum := by decide
  have hdescent : baseEnd_1741902 < baseStart_1741902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1741978 : List Nat := [3, 1, 1, 5, 1, 10]
def baseStart_1741978 : Nat := 118140960795 + 1741978 * 2 ^ 59
def prefixEnd_1741978 : Nat := 4983230072969 + 3 ^ 40 * 1741978 * 2
def baseEnd_1741978 : Nat := 14723818988607254926153

theorem tailTrace_1741978 : CollatzResearch.WordTrace tailWord_1741978 prefixEnd_1741978 14723818988607254926153 := by
  unfold tailWord_1741978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883789320779671750458647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42356771522079124667889725 15883789320779671750458647)
  ·
    refine ⟨23825683981169507625687971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15883789320779671750458647 23825683981169507625687971)
    ·
      refine ⟨35738525971754261438531957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23825683981169507625687971 35738525971754261438531957)
      ·
        refine ⟨3350486809851962009862371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35738525971754261438531957 3350486809851962009862371)
        ·
          refine ⟨5025730214777943014793557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3350486809851962009862371 5025730214777943014793557)
          ·
            refine ⟨14723818988607254926153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5025730214777943014793557 14723818988607254926153)
            ·
              rfl

theorem cell21_1741978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 10].length) (baseStart_1741978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1741978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1741978 prefixEnd_1741978 := by exact prefixLift 1741978
  have htrace : WordTrace (prefixWord ++ tailWord_1741978) baseStart_1741978 baseEnd_1741978 := by
    simpa [prefixWord, tailWord_1741978, baseEnd_1741978] using wordTrace_append hprefix tailTrace_1741978
  have hstable : (prefixWord ++ tailWord_1741978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1741978).length < 2 ^ (prefixWord ++ tailWord_1741978).sum := by decide
  have hdescent : baseEnd_1741978 < baseStart_1741978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1741978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742009 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 5]
def baseStart_1742009 : Nat := 118140960795 + 1742009 * 2 ^ 59
def prefixEnd_1742009 : Nat := 4983230072969 + 3 ^ 40 * 1742009 * 2
def baseEnd_1742009 : Nat := 397550187314746717989401

theorem tailTrace_1742009 : CollatzResearch.WordTrace tailWord_1742009 prefixEnd_1742009 397550187314746717989401 := by
  unfold tailWord_1742009
  simp only [CollatzResearch.WordTrace]
  refine ⟨63536287946006379296213081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42357525297337586197475387 63536287946006379296213081)
  ·
    refine ⟨47652215959504784472159811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63536287946006379296213081 47652215959504784472159811)
    ·
      refine ⟨71478323939257176708239717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47652215959504784472159811 71478323939257176708239717)
      ·
        refine ⟨13402185738610720632794947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71478323939257176708239717 13402185738610720632794947)
        ·
          refine ⟨20103278607916080949192421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13402185738610720632794947 20103278607916080949192421)
          ·
            refine ⟨3769364738984265177973579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20103278607916080949192421 3769364738984265177973579)
            ·
              refine ⟨5654047108476397766960369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769364738984265177973579 5654047108476397766960369)
              ·
                refine ⟨4240535331357298325220277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5654047108476397766960369 4240535331357298325220277)
                ·
                  refine ⟨397550187314746717989401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4240535331357298325220277 397550187314746717989401)
                  ·
                    rfl

theorem cell21_1742009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_1742009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742009 prefixEnd_1742009 := by exact prefixLift 1742009
  have htrace : WordTrace (prefixWord ++ tailWord_1742009) baseStart_1742009 baseEnd_1742009 := by
    simpa [prefixWord, tailWord_1742009, baseEnd_1742009] using wordTrace_append hprefix tailTrace_1742009
  have hstable : (prefixWord ++ tailWord_1742009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742009).length < 2 ^ (prefixWord ++ tailWord_1742009).sum := by decide
  have hdescent : baseEnd_1742009 < baseStart_1742009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742026 : List Nat := [3, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_1742026 : Nat := 118140960795 + 1742026 * 2 ^ 59
def prefixEnd_1742026 : Nat := 4983230072969 + 3 ^ 40 * 1742026 * 2
def baseEnd_1742026 : Nat := 397554066946358466206033

theorem tailTrace_1742026 : CollatzResearch.WordTrace tailWord_1742026 prefixEnd_1742026 397554066946358466206033 := by
  unfold tailWord_1742026
  simp only [CollatzResearch.WordTrace]
  refine ⟨15884226996736197799895483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42357938657963194133054621 15884226996736197799895483)
  ·
    refine ⟨23826340495104296699843225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15884226996736197799895483 23826340495104296699843225)
    ·
      refine ⟨17869755371328222524882419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23826340495104296699843225 17869755371328222524882419)
      ·
        refine ⟨26804633056992333787323629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17869755371328222524882419 26804633056992333787323629)
        ·
          refine ⟨10051737396372125170246361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26804633056992333787323629 10051737396372125170246361)
          ·
            refine ⟨7538803047279093877684771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10051737396372125170246361 7538803047279093877684771)
            ·
              refine ⟨11308204570918640816527157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7538803047279093877684771 11308204570918640816527157)
              ·
                refine ⟨1060144178523622576549421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11308204570918640816527157 1060144178523622576549421)
                ·
                  refine ⟨397554066946358466206033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1060144178523622576549421 397554066946358466206033)
                  ·
                    rfl

theorem cell21_1742026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_1742026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742026 prefixEnd_1742026 := by exact prefixLift 1742026
  have htrace : WordTrace (prefixWord ++ tailWord_1742026) baseStart_1742026 baseEnd_1742026 := by
    simpa [prefixWord, tailWord_1742026, baseEnd_1742026] using wordTrace_append hprefix tailTrace_1742026
  have hstable : (prefixWord ++ tailWord_1742026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742026).length < 2 ^ (prefixWord ++ tailWord_1742026).sum := by decide
  have hdescent : baseEnd_1742026 < baseStart_1742026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742040 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_1742040 : Nat := 118140960795 + 1742040 * 2 ^ 59
def prefixEnd_1742040 : Nat := 4983230072969 + 3 ^ 40 * 1742040 * 2
def baseEnd_1742040 : Nat := 397557261937097552972671

theorem tailTrace_1742040 : CollatzResearch.WordTrace tailWord_1742040 prefixEnd_1742040 397557261937097552972671 := by
  unfold tailWord_1742040
  simp only [CollatzResearch.WordTrace]
  refine ⟨31768709304447035795295787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42358279072596047727061049 31768709304447035795295787)
  ·
    refine ⟨47653063956670553692943681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31768709304447035795295787 47653063956670553692943681)
    ·
      refine ⟨35739797967502915269707761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47653063956670553692943681 35739797967502915269707761)
      ·
        refine ⟨26804848475627186452280821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35739797967502915269707761 26804848475627186452280821)
        ·
          refine ⟨2512954544590048729901327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26804848475627186452280821 2512954544590048729901327)
          ·
            refine ⟨3769431816885073094851991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512954544590048729901327 3769431816885073094851991)
            ·
              refine ⟨5654147725327609642277987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3769431816885073094851991 5654147725327609642277987)
              ·
                refine ⟨8481221587991414463416981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5654147725327609642277987 8481221587991414463416981)
                ·
                  refine ⟨397557261937097552972671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8481221587991414463416981 397557261937097552972671)
                  ·
                    rfl

theorem cell21_1742040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_1742040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742040 prefixEnd_1742040 := by exact prefixLift 1742040
  have htrace : WordTrace (prefixWord ++ tailWord_1742040) baseStart_1742040 baseEnd_1742040 := by
    simpa [prefixWord, tailWord_1742040, baseEnd_1742040] using wordTrace_append hprefix tailTrace_1742040
  have hstable : (prefixWord ++ tailWord_1742040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742040).length < 2 ^ (prefixWord ++ tailWord_1742040).sum := by decide
  have hdescent : baseEnd_1742040 < baseStart_1742040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742116 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_1742116 : Nat := 118140960795 + 1742116 * 2 ^ 59
def prefixEnd_1742116 : Nat := 4983230072969 + 3 ^ 40 * 1742116 * 2
def baseEnd_1742116 : Nat := 397574606172538309705849

theorem tailTrace_1742116 : CollatzResearch.WordTrace tailWord_1742116 prefixEnd_1742116 397574606172538309705849 := by
  unfold tailWord_1742116
  simp only [CollatzResearch.WordTrace]
  refine ⟨31770095278309368285179101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42360127037745824380238801 31770095278309368285179101)
  ·
    refine ⟨11913785729366013106942163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31770095278309368285179101 11913785729366013106942163)
    ·
      refine ⟨17870678594049019660413245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11913785729366013106942163 17870678594049019660413245)
      ·
        refine ⟨6701504472768382372654967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17870678594049019660413245 6701504472768382372654967)
        ·
          refine ⟨10052256709152573558982451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701504472768382372654967 10052256709152573558982451)
          ·
            refine ⟨15078385063728860338473677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10052256709152573558982451 15078385063728860338473677)
            ·
              refine ⟨5654394398898322626927629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15078385063728860338473677 5654394398898322626927629)
              ·
                refine ⟨2120397899586870985097861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5654394398898322626927629 2120397899586870985097861)
                ·
                  refine ⟨397574606172538309705849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2120397899586870985097861 397574606172538309705849)
                  ·
                    rfl

theorem cell21_1742116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_1742116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742116 prefixEnd_1742116 := by exact prefixLift 1742116
  have htrace : WordTrace (prefixWord ++ tailWord_1742116) baseStart_1742116 baseEnd_1742116 := by
    simpa [prefixWord, tailWord_1742116, baseEnd_1742116] using wordTrace_append hprefix tailTrace_1742116
  have hstable : (prefixWord ++ tailWord_1742116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742116).length < 2 ^ (prefixWord ++ tailWord_1742116).sum := by decide
  have hdescent : baseEnd_1742116 < baseStart_1742116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742130 : List Nat := [3, 2, 1, 1, 4, 1, 2, 7]
def baseStart_1742130 : Nat := 118140960795 + 1742130 * 2 ^ 59
def prefixEnd_1742130 : Nat := 4983230072969 + 3 ^ 40 * 1742130 * 2
def baseEnd_1742130 : Nat := 132525933721092465490829

theorem tailTrace_1742130 : CollatzResearch.WordTrace tailWord_1742130 prefixEnd_1742130 132525933721092465490829 := by
  unfold tailWord_1742130
  simp only [CollatzResearch.WordTrace]
  refine ⟨15885175294642004240341961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42360467452378677974245229 15885175294642004240341961)
  ·
    refine ⟨11913881470981503180256471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15885175294642004240341961 11913881470981503180256471)
    ·
      refine ⟨17870822206472254770384707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11913881470981503180256471 17870822206472254770384707)
      ·
        refine ⟨26806233309708382155577061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17870822206472254770384707 26806233309708382155577061)
        ·
          refine ⟨5026168745570321654170699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26806233309708382155577061 5026168745570321654170699)
          ·
            refine ⟨7539253118355482481256049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5026168745570321654170699 7539253118355482481256049)
            ·
              refine ⟨5654439838766611860942037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7539253118355482481256049 5654439838766611860942037)
              ·
                refine ⟨132525933721092465490829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5654439838766611860942037 132525933721092465490829)
                ·
                  rfl

theorem cell21_1742130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_1742130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742130 prefixEnd_1742130 := by exact prefixLift 1742130
  have htrace : WordTrace (prefixWord ++ tailWord_1742130) baseStart_1742130 baseEnd_1742130 := by
    simpa [prefixWord, tailWord_1742130, baseEnd_1742130] using wordTrace_append hprefix tailTrace_1742130
  have hstable : (prefixWord ++ tailWord_1742130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742130).length < 2 ^ (prefixWord ++ tailWord_1742130).sum := by decide
  have hdescent : baseEnd_1742130 < baseStart_1742130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742237 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1742237 : Nat := 118140960795 + 1742237 * 2 ^ 59
def prefixEnd_1742237 : Nat := 4983230072969 + 3 ^ 40 * 1742237 * 2
def baseEnd_1742237 : Nat := 397602220021068988188935

theorem tailTrace_1742237 : CollatzResearch.WordTrace tailWord_1742237 prefixEnd_1742237 397602220021068988188935 := by
  unfold tailWord_1742237
  simp only [CollatzResearch.WordTrace]
  refine ⟨63544603789180374235512965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42363069192786916157008643 63544603789180374235512965)
  ·
    refine ⟨11914613210471320169158681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63544603789180374235512965 11914613210471320169158681)
    ·
      refine ⟨8935959907853490126869011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11914613210471320169158681 8935959907853490126869011)
      ·
        refine ⟨13403939861780235190303517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8935959907853490126869011 13403939861780235190303517)
        ·
          refine ⟨5026477448167588196363819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13403939861780235190303517 5026477448167588196363819)
          ·
            refine ⟨7539716172251382294545729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5026477448167588196363819 7539716172251382294545729)
            ·
              refine ⟨5654787129188536720909297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7539716172251382294545729 5654787129188536720909297)
              ·
                refine ⟨4241090346891402540681973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5654787129188536720909297 4241090346891402540681973)
                ·
                  refine ⟨397602220021068988188935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4241090346891402540681973 397602220021068988188935)
                  ·
                    rfl

theorem cell21_1742237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1742237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742237 prefixEnd_1742237 := by exact prefixLift 1742237
  have htrace : WordTrace (prefixWord ++ tailWord_1742237) baseStart_1742237 baseEnd_1742237 := by
    simpa [prefixWord, tailWord_1742237, baseEnd_1742237] using wordTrace_append hprefix tailTrace_1742237
  have hstable : (prefixWord ++ tailWord_1742237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742237).length < 2 ^ (prefixWord ++ tailWord_1742237).sum := by decide
  have hdescent : baseEnd_1742237 < baseStart_1742237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742274 : List Nat := [3, 5, 2, 1, 1, 1, 2, 6]
def baseStart_1742274 : Nat := 118140960795 + 1742274 * 2 ^ 59
def prefixEnd_1742274 : Nat := 4983230072969 + 3 ^ 40 * 1742274 * 2
def baseEnd_1742274 : Nat := 132536887975055048690731

theorem tailTrace_1742274 : CollatzResearch.WordTrace tailWord_1742274 prefixEnd_1742274 132536887975055048690731 := by
  unfold tailWord_1742274
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886488322511582388652469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42363968860030886369739917 15886488322511582388652469)
  ·
    refine ⟨1489358280235460848936169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15886488322511582388652469 1489358280235460848936169)
    ·
      refine ⟨1117018710176595636702127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1489358280235460848936169 1117018710176595636702127)
      ·
        refine ⟨1675528065264893455053191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117018710176595636702127 1675528065264893455053191)
        ·
          refine ⟨2513292097897340182579787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675528065264893455053191 2513292097897340182579787)
          ·
            refine ⟨3769938146846010273869681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513292097897340182579787 3769938146846010273869681)
            ·
              refine ⟨2827453610134507705402261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769938146846010273869681 2827453610134507705402261)
              ·
                refine ⟨132536887975055048690731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2827453610134507705402261 132536887975055048690731)
                ·
                  rfl

theorem cell21_1742274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_1742274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742274 prefixEnd_1742274 := by exact prefixLift 1742274
  have htrace : WordTrace (prefixWord ++ tailWord_1742274) baseStart_1742274 baseEnd_1742274 := by
    simpa [prefixWord, tailWord_1742274, baseEnd_1742274] using wordTrace_append hprefix tailTrace_1742274
  have hstable : (prefixWord ++ tailWord_1742274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742274).length < 2 ^ (prefixWord ++ tailWord_1742274).sum := by decide
  have hdescent : baseEnd_1742274 < baseStart_1742274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742282 : List Nat := [3, 1, 2, 1, 2, 4, 2, 6]
def baseStart_1742282 : Nat := 118140960795 + 1742282 * 2 ^ 59
def prefixEnd_1742282 : Nat := 4983230072969 + 3 ^ 40 * 1742282 * 2
def baseEnd_1742282 : Nat := 132537496544719636646281

theorem tailTrace_1742282 : CollatzResearch.WordTrace tailWord_1742282 prefixEnd_1742282 132537496544719636646281 := by
  unfold tailWord_1742282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886561268504336730225275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42364163382678231280600733 15886561268504336730225275)
  ·
    refine ⟨23829841902756505095337913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15886561268504336730225275 23829841902756505095337913)
    ·
      refine ⟨17872381427067378821503435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23829841902756505095337913 17872381427067378821503435)
      ·
        refine ⟨26808572140601068232255153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17872381427067378821503435 26808572140601068232255153)
        ·
          refine ⟨20106429105450801174191365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26808572140601068232255153 20106429105450801174191365)
          ·
            refine ⟨3769955457272025220160881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20106429105450801174191365 3769955457272025220160881)
            ·
              refine ⟨2827466592954018915120661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769955457272025220160881 2827466592954018915120661)
              ·
                refine ⟨132537496544719636646281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2827466592954018915120661 132537496544719636646281)
                ·
                  rfl

theorem cell21_1742282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_1742282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742282 prefixEnd_1742282 := by exact prefixLift 1742282
  have htrace : WordTrace (prefixWord ++ tailWord_1742282) baseStart_1742282 baseEnd_1742282 := by
    simpa [prefixWord, tailWord_1742282, baseEnd_1742282] using wordTrace_append hprefix tailTrace_1742282
  have hstable : (prefixWord ++ tailWord_1742282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742282).length < 2 ^ (prefixWord ++ tailWord_1742282).sum := by decide
  have hdescent : baseEnd_1742282 < baseStart_1742282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742296 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_1742296 : Nat := 118140960795 + 1742296 * 2 ^ 59
def prefixEnd_1742296 : Nat := 4983230072969 + 3 ^ 40 * 1742296 * 2
def baseEnd_1742296 : Nat := 397615684624897996705481

theorem tailTrace_1742296 : CollatzResearch.WordTrace tailWord_1742296 prefixEnd_1742296 397615684624897996705481 := by
  unfold tailWord_1742296
  simp only [CollatzResearch.WordTrace]
  refine ⟨31773377847983313655955371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42364503797311084874607161 31773377847983313655955371)
  ·
    refine ⟨47660066771974970483933057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31773377847983313655955371 47660066771974970483933057)
    ·
      refine ⟨35745050078981227862949793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47660066771974970483933057 35745050078981227862949793)
      ·
        refine ⟨26808787559235920897212345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35745050078981227862949793 26808787559235920897212345)
        ·
          refine ⟨20106590669426940672909259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26808787559235920897212345 20106590669426940672909259)
          ·
            refine ⟨30159886004140411009363889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20106590669426940672909259 30159886004140411009363889)
            ·
              refine ⟨22619914503105308257022917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30159886004140411009363889 22619914503105308257022917)
              ·
                refine ⟨4241233969332245298191797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22619914503105308257022917 4241233969332245298191797)
                ·
                  refine ⟨397615684624897996705481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4241233969332245298191797 397615684624897996705481)
                  ·
                    rfl

theorem cell21_1742296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_1742296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742296 prefixEnd_1742296 := by exact prefixLift 1742296
  have htrace : WordTrace (prefixWord ++ tailWord_1742296) baseStart_1742296 baseEnd_1742296 := by
    simpa [prefixWord, tailWord_1742296, baseEnd_1742296] using wordTrace_append hprefix tailTrace_1742296
  have hstable : (prefixWord ++ tailWord_1742296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742296).length < 2 ^ (prefixWord ++ tailWord_1742296).sum := by decide
  have hdescent : baseEnd_1742296 < baseStart_1742296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742389 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 5]
def baseStart_1742389 : Nat := 118140960795 + 1742389 * 2 ^ 59
def prefixEnd_1742389 : Nat := 4983230072969 + 3 ^ 40 * 1742389 * 2
def baseEnd_1742389 : Nat := 397636908491950501655291

theorem tailTrace_1742389 : CollatzResearch.WordTrace tailWord_1742389 prefixEnd_1742389 397636908491950501655291 := by
  unfold tailWord_1742389
  simp only [CollatzResearch.WordTrace]
  refine ⟨63550147684629704195046221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42366765123086469463364147 63550147684629704195046221)
  ·
    refine ⟨23831305381736139073142333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63550147684629704195046221 23831305381736139073142333)
    ·
      refine ⟨8936739518151052152428375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23831305381736139073142333 8936739518151052152428375)
      ·
        refine ⟨13405109277226578228642563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8936739518151052152428375 13405109277226578228642563)
        ·
          refine ⟨20107663915839867342963845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13405109277226578228642563 20107663915839867342963845)
          ·
            refine ⟨3770186984219975126805721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20107663915839867342963845 3770186984219975126805721)
            ·
              refine ⟨2827640238164981345104291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3770186984219975126805721 2827640238164981345104291)
              ·
                refine ⟨4241460357247472017656437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827640238164981345104291 4241460357247472017656437)
                ·
                  refine ⟨397636908491950501655291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4241460357247472017656437 397636908491950501655291)
                  ·
                    rfl

theorem cell21_1742389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_1742389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742389 prefixEnd_1742389 := by exact prefixLift 1742389
  have htrace : WordTrace (prefixWord ++ tailWord_1742389) baseStart_1742389 baseEnd_1742389 := by
    simpa [prefixWord, tailWord_1742389, baseEnd_1742389] using wordTrace_append hprefix tailTrace_1742389
  have hstable : (prefixWord ++ tailWord_1742389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742389).length < 2 ^ (prefixWord ++ tailWord_1742389).sum := by decide
  have hdescent : baseEnd_1742389 < baseStart_1742389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742417 : List Nat := [1, 2, 2, 1, 3, 2, 3, 7]
def baseStart_1742417 : Nat := 118140960795 + 1742417 * 2 ^ 59
def prefixEnd_1742417 : Nat := 4983230072969 + 3 ^ 40 * 1742417 * 2
def baseEnd_1742417 : Nat := 132547766157809558396189

theorem tailTrace_1742417 : CollatzResearch.WordTrace tailWord_1742417 prefixEnd_1742417 132547766157809558396189 := by
  unfold tailWord_1742417
  simp only [CollatzResearch.WordTrace]
  refine ⟨63551168928528264977065505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42367445952352176651377003 63551168928528264977065505)
  ·
    refine ⟨47663376696396198732799129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63551168928528264977065505 47663376696396198732799129)
    ·
      refine ⟨35747532522297149049599347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47663376696396198732799129 35747532522297149049599347)
      ·
        refine ⟨53621298783445723574399021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35747532522297149049599347 53621298783445723574399021)
        ·
          refine ⟨20107987043792146340399633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53621298783445723574399021 20107987043792146340399633)
          ·
            refine ⟨15080990282844109755299725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20107987043792146340399633 15080990282844109755299725)
            ·
              refine ⟨5655371356066541158237397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15080990282844109755299725 5655371356066541158237397)
              ·
                refine ⟨132547766157809558396189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5655371356066541158237397 132547766157809558396189)
                ·
                  rfl

theorem cell21_1742417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 7].length) (baseStart_1742417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742417 prefixEnd_1742417 := by exact prefixLift 1742417
  have htrace : WordTrace (prefixWord ++ tailWord_1742417) baseStart_1742417 baseEnd_1742417 := by
    simpa [prefixWord, tailWord_1742417, baseEnd_1742417] using wordTrace_append hprefix tailTrace_1742417
  have hstable : (prefixWord ++ tailWord_1742417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742417).length < 2 ^ (prefixWord ++ tailWord_1742417).sum := by decide
  have hdescent : baseEnd_1742417 < baseStart_1742417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742454 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1742454 : Nat := 118140960795 + 1742454 * 2 ^ 59
def prefixEnd_1742454 : Nat := 4983230072969 + 3 ^ 40 * 1742454 * 2
def baseEnd_1742454 : Nat := 397651742377524833071825

theorem tailTrace_1742454 : CollatzResearch.WordTrace tailWord_1742454 prefixEnd_1742454 397651742377524833071825 := by
  unfold tailWord_1742454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972032401837138768510151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42368345619596146864108277 3972032401837138768510151)
  ·
    refine ⟨5958048602755708152765227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3972032401837138768510151 5958048602755708152765227)
    ·
      refine ⟨8937072904133562229147841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5958048602755708152765227 8937072904133562229147841)
      ·
        refine ⟨6702804678100171671860881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8937072904133562229147841 6702804678100171671860881)
        ·
          refine ⟨5027103508575128753895661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6702804678100171671860881 5027103508575128753895661)
          ·
            refine ⟨1885163815715673282710873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5027103508575128753895661 1885163815715673282710873)
            ·
              refine ⟨1413872861786754962033155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885163815715673282710873 1413872861786754962033155)
              ·
                refine ⟨2120809292680132443049733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413872861786754962033155 2120809292680132443049733)
                ·
                  refine ⟨397651742377524833071825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2120809292680132443049733 397651742377524833071825)
                  ·
                    rfl

theorem cell21_1742454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1742454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742454 prefixEnd_1742454 := by exact prefixLift 1742454
  have htrace : WordTrace (prefixWord ++ tailWord_1742454) baseStart_1742454 baseEnd_1742454 := by
    simpa [prefixWord, tailWord_1742454, baseEnd_1742454] using wordTrace_append hprefix tailTrace_1742454
  have hstable : (prefixWord ++ tailWord_1742454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742454).length < 2 ^ (prefixWord ++ tailWord_1742454).sum := by decide
  have hdescent : baseEnd_1742454 < baseStart_1742454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742496 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_1742496 : Nat := 118140960795 + 1742496 * 2 ^ 59
def prefixEnd_1742496 : Nat := 4983230072969 + 3 ^ 40 * 1742496 * 2
def baseEnd_1742496 : Nat := 397661327349742093371739

theorem tailTrace_1742496 : CollatzResearch.WordTrace tailWord_1742496 prefixEnd_1742496 397661327349742093371739 := by
  unfold tailWord_1742496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31777025147621030734595671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42369366863494707646127561 31777025147621030734595671)
  ·
    refine ⟨47665537721431546101893507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31777025147621030734595671 47665537721431546101893507)
    ·
      refine ⟨71498306582147319152840261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47665537721431546101893507 71498306582147319152840261)
      ·
        refine ⟨13405932484152622341157549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71498306582147319152840261 13405932484152622341157549)
        ·
          refine ⟨5027224681557233377934081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13405932484152622341157549 5027224681557233377934081)
          ·
            refine ⟨3770418511167925033450561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5027224681557233377934081 3770418511167925033450561)
            ·
              refine ⟨2827813883375943775087921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3770418511167925033450561 2827813883375943775087921)
              ·
                refine ⟨2120860412531957831315941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2827813883375943775087921 2120860412531957831315941)
                ·
                  refine ⟨397661327349742093371739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2120860412531957831315941 397661327349742093371739)
                  ·
                    rfl

theorem cell21_1742496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_1742496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742496 prefixEnd_1742496 := by exact prefixLift 1742496
  have htrace : WordTrace (prefixWord ++ tailWord_1742496) baseStart_1742496 baseEnd_1742496 := by
    simpa [prefixWord, tailWord_1742496, baseEnd_1742496] using wordTrace_append hprefix tailTrace_1742496
  have hstable : (prefixWord ++ tailWord_1742496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742496).length < 2 ^ (prefixWord ++ tailWord_1742496).sum := by decide
  have hdescent : baseEnd_1742496 < baseStart_1742496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742524 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_1742524 : Nat := 118140960795 + 1742524 * 2 ^ 59
def prefixEnd_1742524 : Nat := 4983230072969 + 3 ^ 40 * 1742524 * 2
def baseEnd_1742524 : Nat := 397667717331220266905015

theorem tailTrace_1742524 : CollatzResearch.WordTrace tailWord_1742524 prefixEnd_1742524 397667717331220266905015 := by
  unfold tailWord_1742524
  simp only [CollatzResearch.WordTrace]
  refine ⟨31777535769570311125605313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42370047692760414834140417 31777535769570311125605313)
  ·
    refine ⟨23833151827177733344203985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31777535769570311125605313 23833151827177733344203985)
    ·
      refine ⟨17874863870383300008152989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23833151827177733344203985 17874863870383300008152989)
      ·
        refine ⟨6703073951393737503057371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17874863870383300008152989 6703073951393737503057371)
        ·
          refine ⟨10054610927090606254586057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703073951393737503057371 10054610927090606254586057)
          ·
            refine ⟨7540958195317954690939543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10054610927090606254586057 7540958195317954690939543)
            ·
              refine ⟨11311437292976932036409315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7540958195317954690939543 11311437292976932036409315)
              ·
                refine ⟨16967155939465398054613973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11311437292976932036409315 16967155939465398054613973)
                ·
                  refine ⟨397667717331220266905015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16967155939465398054613973 397667717331220266905015)
                  ·
                    rfl

theorem cell21_1742524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_1742524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742524 prefixEnd_1742524 := by exact prefixLift 1742524
  have htrace : WordTrace (prefixWord ++ tailWord_1742524) baseStart_1742524 baseEnd_1742524 := by
    simpa [prefixWord, tailWord_1742524, baseEnd_1742524] using wordTrace_append hprefix tailTrace_1742524
  have hstable : (prefixWord ++ tailWord_1742524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742524).length < 2 ^ (prefixWord ++ tailWord_1742524).sum := by decide
  have hdescent : baseEnd_1742524 < baseStart_1742524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742668 : List Nat := [2, 2, 1, 3, 5, 1, 2, 2, 3]
def baseStart_1742668 : Nat := 118140960795 + 1742668 * 2 ^ 59
def prefixEnd_1742668 : Nat := 4983230072969 + 3 ^ 40 * 1742668 * 2
def baseEnd_1742668 : Nat := 397700580093108016504721

theorem tailTrace_1742668 : CollatzResearch.WordTrace tailWord_1742668 prefixEnd_1742668 397700580093108016504721 := by
  unfold tailWord_1742668
  simp only [CollatzResearch.WordTrace]
  refine ⟨31780161825309467422226329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42373549100412623229635105 31780161825309467422226329)
  ·
    refine ⟨23835121368982100566669747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31780161825309467422226329 23835121368982100566669747)
    ·
      refine ⟨35752682053473150850004621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23835121368982100566669747 35752682053473150850004621)
      ·
        refine ⟨13407255770052431568751733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35752682053473150850004621 13407255770052431568751733)
        ·
          refine ⟨1256930228442415459570475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13407255770052431568751733 1256930228442415459570475)
          ·
            refine ⟨1885395342663623189355713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256930228442415459570475 1885395342663623189355713)
            ·
              refine ⟨1414046506997717392016785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885395342663623189355713 1414046506997717392016785)
              ·
                refine ⟨1060534880248288044012589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414046506997717392016785 1060534880248288044012589)
                ·
                  refine ⟨397700580093108016504721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1060534880248288044012589 397700580093108016504721)
                  ·
                    rfl

theorem cell21_1742668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_1742668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742668 prefixEnd_1742668 := by exact prefixLift 1742668
  have htrace : WordTrace (prefixWord ++ tailWord_1742668) baseStart_1742668 baseEnd_1742668 := by
    simpa [prefixWord, tailWord_1742668, baseEnd_1742668] using wordTrace_append hprefix tailTrace_1742668
  have hstable : (prefixWord ++ tailWord_1742668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742668).length < 2 ^ (prefixWord ++ tailWord_1742668).sum := by decide
  have hdescent : baseEnd_1742668 < baseStart_1742668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742679 : List Nat := [1, 1, 3, 2, 6, 1, 1, 6]
def baseStart_1742679 : Nat := 118140960795 + 1742679 * 2 ^ 59
def prefixEnd_1742679 : Nat := 4983230072969 + 3 ^ 40 * 1742679 * 2
def baseEnd_1742679 : Nat := 132567696814324813940455

theorem tailTrace_1742679 : CollatzResearch.WordTrace tailWord_1742679 prefixEnd_1742679 132567696814324813940455 := by
  unfold tailWord_1742679
  simp only [CollatzResearch.WordTrace]
  refine ⟨63560724853579083723103091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42373816569052722482068727 63560724853579083723103091)
  ·
    refine ⟨95341087280368625584654637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63560724853579083723103091 95341087280368625584654637)
    ·
      refine ⟨35752907730138234594245489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95341087280368625584654637 35752907730138234594245489)
      ·
        refine ⟨26814680797603675945684117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35752907730138234594245489 26814680797603675945684117)
        ·
          refine ⟨1256938162387672309953943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26814680797603675945684117 1256938162387672309953943)
          ·
            refine ⟨1885407243581508464930915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256938162387672309953943 1885407243581508464930915)
            ·
              refine ⟨2828110865372262697396373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885407243581508464930915 2828110865372262697396373)
              ·
                refine ⟨132567696814324813940455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2828110865372262697396373 132567696814324813940455)
                ·
                  rfl

theorem cell21_1742679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 6].length) (baseStart_1742679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742679 prefixEnd_1742679 := by exact prefixLift 1742679
  have htrace : WordTrace (prefixWord ++ tailWord_1742679) baseStart_1742679 baseEnd_1742679 := by
    simpa [prefixWord, tailWord_1742679, baseEnd_1742679] using wordTrace_append hprefix tailTrace_1742679
  have hstable : (prefixWord ++ tailWord_1742679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742679).length < 2 ^ (prefixWord ++ tailWord_1742679).sum := by decide
  have hdescent : baseEnd_1742679 < baseStart_1742679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742772 : List Nat := [2, 5, 2, 1, 3, 1, 7]
def baseStart_1742772 : Nat := 118140960795 + 1742772 * 2 ^ 59
def prefixEnd_1742772 : Nat := 4983230072969 + 3 ^ 40 * 1742772 * 2
def baseEnd_1742772 : Nat := 44191590478891882974575

theorem tailTrace_1742772 : CollatzResearch.WordTrace tailWord_1742772 prefixEnd_1742772 44191590478891882974575 := by
  unfold tailWord_1742772
  simp only [CollatzResearch.WordTrace]
  refine ⟨31782058421121080303119285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42376077894828107070825713 31782058421121080303119285)
  ·
    refine ⟨2979567976980101278417433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31782058421121080303119285 2979567976980101278417433)
    ·
      refine ⟨2234675982735075958813075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2979567976980101278417433 2234675982735075958813075)
      ·
        refine ⟨3352013974102613938219613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234675982735075958813075 3352013974102613938219613)
        ·
          refine ⟨1257005240288480226832355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3352013974102613938219613 1257005240288480226832355)
          ·
            refine ⟨1885507860432720340248533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257005240288480226832355 1885507860432720340248533)
            ·
              refine ⟨44191590478891882974575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1885507860432720340248533 44191590478891882974575)
              ·
                rfl

theorem cell21_1742772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 7].length) (baseStart_1742772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742772 prefixEnd_1742772 := by exact prefixLift 1742772
  have htrace : WordTrace (prefixWord ++ tailWord_1742772) baseStart_1742772 baseEnd_1742772 := by
    simpa [prefixWord, tailWord_1742772, baseEnd_1742772] using wordTrace_append hprefix tailTrace_1742772
  have hstable : (prefixWord ++ tailWord_1742772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742772).length < 2 ^ (prefixWord ++ tailWord_1742772).sum := by decide
  have hdescent : baseEnd_1742772 < baseStart_1742772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742949 : List Nat := [1, 3, 1, 3, 2, 4, 7]
def baseStart_1742949 : Nat := 118140960795 + 1742949 * 2 ^ 59
def prefixEnd_1742949 : Nat := 4983230072969 + 3 ^ 40 * 1742949 * 2
def baseEnd_1742949 : Nat := 44196078680168219146757

theorem tailTrace_1742949 : CollatzResearch.WordTrace tailWord_1742949 prefixEnd_1742949 44196078680168219146757 := by
  unfold tailWord_1742949
  simp only [CollatzResearch.WordTrace]
  refine ⟨63570572562600919835431901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42380381708400613223621267 63570572562600919835431901)
  ·
    refine ⟨23838964710975344938286963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63570572562600919835431901 23838964710975344938286963)
    ·
      refine ⟨35758447066463017407430445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23838964710975344938286963 35758447066463017407430445)
      ·
        refine ⟨13409417649923631527786417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35758447066463017407430445 13409417649923631527786417)
        ·
          refine ⟨10057063237442723645839813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13409417649923631527786417 10057063237442723645839813)
          ·
            refine ⟨1885699357020510683594965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10057063237442723645839813 1885699357020510683594965)
            ·
              refine ⟨44196078680168219146757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1885699357020510683594965 44196078680168219146757)
              ·
                rfl

theorem cell21_1742949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 7].length) (baseStart_1742949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742949 prefixEnd_1742949 := by exact prefixLift 1742949
  have htrace : WordTrace (prefixWord ++ tailWord_1742949) baseStart_1742949 baseEnd_1742949 := by
    simpa [prefixWord, tailWord_1742949, baseEnd_1742949] using wordTrace_append hprefix tailTrace_1742949
  have hstable : (prefixWord ++ tailWord_1742949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742949).length < 2 ^ (prefixWord ++ tailWord_1742949).sum := by decide
  have hdescent : baseEnd_1742949 < baseStart_1742949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1742966 : List Nat := [5, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1742966 : Nat := 118140960795 + 1742966 * 2 ^ 59
def prefixEnd_1742966 : Nat := 4983230072969 + 3 ^ 40 * 1742966 * 2
def baseEnd_1742966 : Nat := 132589529251041906845815

theorem tailTrace_1742966 : CollatzResearch.WordTrace tailWord_1742966 prefixEnd_1742966 132589529251041906845815 := by
  unfold tailWord_1742966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973199537721208233675047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42380795069026221159200501 3973199537721208233675047)
  ·
    refine ⟨5959799306581812350512571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3973199537721208233675047 5959799306581812350512571)
    ·
      refine ⟨8939698959872718525768857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5959799306581812350512571 8939698959872718525768857)
      ·
        refine ⟨6704774219904538894326643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8939698959872718525768857 6704774219904538894326643)
        ·
          refine ⟨10057161329856808341489965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6704774219904538894326643 10057161329856808341489965)
          ·
            refine ⟨3771435498696303128058737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10057161329856808341489965 3771435498696303128058737)
            ·
              refine ⟨2828576624022227346044053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3771435498696303128058737 2828576624022227346044053)
              ·
                refine ⟨132589529251041906845815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2828576624022227346044053 132589529251041906845815)
                ·
                  rfl

theorem cell21_1742966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1742966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1742966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1742966 prefixEnd_1742966 := by exact prefixLift 1742966
  have htrace : WordTrace (prefixWord ++ tailWord_1742966) baseStart_1742966 baseEnd_1742966 := by
    simpa [prefixWord, tailWord_1742966, baseEnd_1742966] using wordTrace_append hprefix tailTrace_1742966
  have hstable : (prefixWord ++ tailWord_1742966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1742966).length < 2 ^ (prefixWord ++ tailWord_1742966).sum := by decide
  have hdescent : baseEnd_1742966 < baseStart_1742966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1742966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743008 : List Nat := [2, 1, 1, 4, 2, 11]
def baseStart_1743008 : Nat := 118140960795 + 1743008 * 2 ^ 59
def prefixEnd_1743008 : Nat := 4983230072969 + 3 ^ 40 * 1743008 * 2
def baseEnd_1743008 : Nat := 14732524915753443734717

theorem tailTrace_1743008 : CollatzResearch.WordTrace tailWord_1743008 prefixEnd_1743008 14732524915753443734717 := by
  unfold tailWord_1743008
  simp only [CollatzResearch.WordTrace]
  refine ⟨31786362234693586455914839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42381816312924781941219785 31786362234693586455914839)
  ·
    refine ⟨47679543352040379683872259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31786362234693586455914839 47679543352040379683872259)
    ·
      refine ⟨71519315028060569525808389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47679543352040379683872259 71519315028060569525808389)
      ·
        refine ⟨13409871567761356786089073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71519315028060569525808389 13409871567761356786089073)
        ·
          refine ⟨10057403675821017589566805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13409871567761356786089073 10057403675821017589566805)
          ·
            refine ⟨14732524915753443734717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10057403675821017589566805 14732524915753443734717)
            ·
              rfl

theorem cell21_1743008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 11].length) (baseStart_1743008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743008 prefixEnd_1743008 := by exact prefixLift 1743008
  have htrace : WordTrace (prefixWord ++ tailWord_1743008) baseStart_1743008 baseEnd_1743008 := by
    simpa [prefixWord, tailWord_1743008, baseEnd_1743008] using wordTrace_append hprefix tailTrace_1743008
  have hstable : (prefixWord ++ tailWord_1743008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743008).length < 2 ^ (prefixWord ++ tailWord_1743008).sum := by decide
  have hdescent : baseEnd_1743008 < baseStart_1743008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743084 : List Nat := [2, 2, 1, 1, 2, 3, 2, 8]
def baseStart_1743084 : Nat := 118140960795 + 1743084 * 2 ^ 59
def prefixEnd_1743084 : Nat := 4983230072969 + 3 ^ 40 * 1743084 * 2
def baseEnd_1743084 : Nat := 132598505653594579190179

theorem tailTrace_1743084 : CollatzResearch.WordTrace tailWord_1743084 prefixEnd_1743084 132598505653594579190179 := by
  unfold tailWord_1743084
  simp only [CollatzResearch.WordTrace]
  refine ⟨31787748208555918945798153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42383664278074558594397537 31787748208555918945798153)
  ·
    refine ⟨23840811156416939209348615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31787748208555918945798153 23840811156416939209348615)
    ·
      refine ⟨35761216734625408814022923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23840811156416939209348615 35761216734625408814022923)
      ·
        refine ⟨53641825101938113221034385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35761216734625408814022923 53641825101938113221034385)
        ·
          refine ⟨40231368826453584915775789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53641825101938113221034385 40231368826453584915775789)
          ·
            refine ⟨15086763309920094343415921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40231368826453584915775789 15086763309920094343415921)
            ·
              refine ⟨11315072482440070757561941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15086763309920094343415921 11315072482440070757561941)
              ·
                refine ⟨132598505653594579190179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11315072482440070757561941 132598505653594579190179)
                ·
                  rfl

theorem cell21_1743084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_1743084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743084 prefixEnd_1743084 := by exact prefixLift 1743084
  have htrace : WordTrace (prefixWord ++ tailWord_1743084) baseStart_1743084 baseEnd_1743084 := by
    simpa [prefixWord, tailWord_1743084, baseEnd_1743084] using wordTrace_append hprefix tailTrace_1743084
  have hstable : (prefixWord ++ tailWord_1743084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743084).length < 2 ^ (prefixWord ++ tailWord_1743084).sum := by decide
  have hdescent : baseEnd_1743084 < baseStart_1743084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743160 : List Nat := [2, 1, 2, 1, 3, 1, 4, 7]
def baseStart_1743160 : Nat := 118140960795 + 1743160 * 2 ^ 59
def prefixEnd_1743160 : Nat := 4983230072969 + 3 ^ 40 * 1743160 * 2
def baseEnd_1743160 : Nat := 132604287065408164767905

theorem tailTrace_1743160 : CollatzResearch.WordTrace tailWord_1743160 prefixEnd_1743160 132604287065408164767905 := by
  unfold tailWord_1743160
  simp only [CollatzResearch.WordTrace]
  refine ⟨31789134182418251435681467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42385512243224335247575289 31789134182418251435681467)
  ·
    refine ⟨47683701273627377153522201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31789134182418251435681467 47683701273627377153522201)
    ·
      refine ⟨35762775955220532865141651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47683701273627377153522201 35762775955220532865141651)
      ·
        refine ⟨53644163932830799297712477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35762775955220532865141651 53644163932830799297712477)
        ·
          refine ⟨20116561474811549736642179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53644163932830799297712477 20116561474811549736642179)
          ·
            refine ⟨30174842212217324604963269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20116561474811549736642179 30174842212217324604963269)
            ·
              refine ⟨5657782914790748363430613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30174842212217324604963269 5657782914790748363430613)
              ·
                refine ⟨132604287065408164767905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5657782914790748363430613 132604287065408164767905)
                ·
                  rfl

theorem cell21_1743160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_1743160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743160 prefixEnd_1743160 := by exact prefixLift 1743160
  have htrace : WordTrace (prefixWord ++ tailWord_1743160) baseStart_1743160 baseEnd_1743160 := by
    simpa [prefixWord, tailWord_1743160, baseEnd_1743160] using wordTrace_append hprefix tailTrace_1743160
  have hstable : (prefixWord ++ tailWord_1743160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743160).length < 2 ^ (prefixWord ++ tailWord_1743160).sum := by decide
  have hdescent : baseEnd_1743160 < baseStart_1743160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743191 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 5]
def baseStart_1743191 : Nat := 118140960795 + 1743191 * 2 ^ 59
def prefixEnd_1743191 : Nat := 4983230072969 + 3 ^ 40 * 1743191 * 2
def baseEnd_1743191 : Nat := 397819935818575329286985

theorem tailTrace_1743191 : CollatzResearch.WordTrace tailWord_1743191 prefixEnd_1743191 397819935818575329286985 := by
  unfold tailWord_1743191
  simp only [CollatzResearch.WordTrace]
  refine ⟨63579399027724195165741427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42386266018482796777160951 63579399027724195165741427)
  ·
    refine ⟨95369098541586292748612141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63579399027724195165741427 95369098541586292748612141)
    ·
      refine ⟨35763411953094859780729553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95369098541586292748612141 35763411953094859780729553)
      ·
        refine ⟨26822558964821144835547165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35763411953094859780729553 26822558964821144835547165)
        ·
          refine ⟨10058459611807929313330187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26822558964821144835547165 10058459611807929313330187)
          ·
            refine ⟨15087689417711893969995281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10058459611807929313330187 15087689417711893969995281)
            ·
              refine ⟨11315767063283920477496461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15087689417711893969995281 11315767063283920477496461)
              ·
                refine ⟨4243412648731470179061173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11315767063283920477496461 4243412648731470179061173)
                ·
                  refine ⟨397819935818575329286985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4243412648731470179061173 397819935818575329286985)
                  ·
                    rfl

theorem cell21_1743191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_1743191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743191 prefixEnd_1743191 := by exact prefixLift 1743191
  have htrace : WordTrace (prefixWord ++ tailWord_1743191) baseStart_1743191 baseEnd_1743191 := by
    simpa [prefixWord, tailWord_1743191, baseEnd_1743191] using wordTrace_append hprefix tailTrace_1743191
  have hstable : (prefixWord ++ tailWord_1743191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743191).length < 2 ^ (prefixWord ++ tailWord_1743191).sum := by decide
  have hdescent : baseEnd_1743191 < baseStart_1743191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743208 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_1743208 : Nat := 118140960795 + 1743208 * 2 ^ 59
def prefixEnd_1743208 : Nat := 4983230072969 + 3 ^ 40 * 1743208 * 2
def baseEnd_1743208 : Nat := 397823815450187077503617

theorem tailTrace_1743208 : CollatzResearch.WordTrace tailWord_1743208 prefixEnd_1743208 397823815450187077503617 := by
  unfold tailWord_1743208
  simp only [CollatzResearch.WordTrace]
  refine ⟨31790009534331303534555139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42386679379108404712740185 31790009534331303534555139)
  ·
    refine ⟨47685014301496955301832709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31790009534331303534555139 47685014301496955301832709)
    ·
      refine ⟨8940940181530679119093633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47685014301496955301832709 8940940181530679119093633)
      ·
        refine ⟨6705705136148009339320225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8940940181530679119093633 6705705136148009339320225)
        ·
          refine ⟨5029278852111007004490169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6705705136148009339320225 5029278852111007004490169)
          ·
            refine ⟨3771959139083255253367627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5029278852111007004490169 3771959139083255253367627)
            ·
              refine ⟨5657938708624882880051441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771959139083255253367627 5657938708624882880051441)
              ·
                refine ⟨4243454031468662160038581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657938708624882880051441 4243454031468662160038581)
                ·
                  refine ⟨397823815450187077503617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4243454031468662160038581 397823815450187077503617)
                  ·
                    rfl

theorem cell21_1743208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_1743208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743208 prefixEnd_1743208 := by exact prefixLift 1743208
  have htrace : WordTrace (prefixWord ++ tailWord_1743208) baseStart_1743208 baseEnd_1743208 := by
    simpa [prefixWord, tailWord_1743208, baseEnd_1743208] using wordTrace_append hprefix tailTrace_1743208
  have hstable : (prefixWord ++ tailWord_1743208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743208).length < 2 ^ (prefixWord ++ tailWord_1743208).sum := by decide
  have hdescent : baseEnd_1743208 < baseStart_1743208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743236 : List Nat := [2, 3, 2, 1, 1, 2, 10]
def baseStart_1743236 : Nat := 118140960795 + 1743236 * 2 ^ 59
def prefixEnd_1743236 : Nat := 4983230072969 + 3 ^ 40 * 1743236 * 2
def baseEnd_1743236 : Nat := 44203356159073916781877

theorem tailTrace_1743236 : CollatzResearch.WordTrace tailWord_1743236 prefixEnd_1743236 44203356159073916781877 := by
  unfold tailWord_1743236
  simp only [CollatzResearch.WordTrace]
  refine ⟨31790520156280583925564781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42387360208374111900753041 31790520156280583925564781)
  ·
    refine ⟨11921445058605218972086793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31790520156280583925564781 11921445058605218972086793)
    ·
      refine ⟨8941083793953914229065095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11921445058605218972086793 8941083793953914229065095)
      ·
        refine ⟨13411625690930871343597643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8941083793953914229065095 13411625690930871343597643)
        ·
          refine ⟨20117438536396307015396465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13411625690930871343597643 20117438536396307015396465)
          ·
            refine ⟨15088078902297230261547349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20117438536396307015396465 15088078902297230261547349)
            ·
              refine ⟨44203356159073916781877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15088078902297230261547349 44203356159073916781877)
              ·
                rfl

theorem cell21_1743236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 10].length) (baseStart_1743236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743236 prefixEnd_1743236 := by exact prefixLift 1743236
  have htrace : WordTrace (prefixWord ++ tailWord_1743236) baseStart_1743236 baseEnd_1743236 := by
    simpa [prefixWord, tailWord_1743236, baseEnd_1743236] using wordTrace_append hprefix tailTrace_1743236
  have hstable : (prefixWord ++ tailWord_1743236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743236).length < 2 ^ (prefixWord ++ tailWord_1743236).sum := by decide
  have hdescent : baseEnd_1743236 < baseStart_1743236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743256 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_1743256 : Nat := 118140960795 + 1743256 * 2 ^ 59
def prefixEnd_1743256 : Nat := 4983230072969 + 3 ^ 40 * 1743256 * 2
def baseEnd_1743256 : Nat := 397834769704149660703519

theorem tailTrace_1743256 : CollatzResearch.WordTrace tailWord_1743256 prefixEnd_1743256 397834769704149660703519 := by
  unfold tailWord_1743256
  simp only [CollatzResearch.WordTrace]
  refine ⟨31790884886244355633428811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42387846514992474177905081 31790884886244355633428811)
  ·
    refine ⟨47686327329366533450143217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31790884886244355633428811 47686327329366533450143217)
    ·
      refine ⟨35764745497024900087607413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47686327329366533450143217 35764745497024900087607413)
      ·
        refine ⟨3352944890346084383213195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35764745497024900087607413 3352944890346084383213195)
        ·
          refine ⟨5029417335519126574819793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352944890346084383213195 5029417335519126574819793)
          ·
            refine ⟨3772063001639344931114845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5029417335519126574819793 3772063001639344931114845)
            ·
              refine ⟨1414523625614754349168067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3772063001639344931114845 1414523625614754349168067)
              ·
                refine ⟨2121785438422131523752101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414523625614754349168067 2121785438422131523752101)
                ·
                  refine ⟨397834769704149660703519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2121785438422131523752101 397834769704149660703519)
                  ·
                    rfl

theorem cell21_1743256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_1743256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743256 prefixEnd_1743256 := by exact prefixLift 1743256
  have htrace : WordTrace (prefixWord ++ tailWord_1743256) baseStart_1743256 baseEnd_1743256 := by
    simpa [prefixWord, tailWord_1743256, baseEnd_1743256] using wordTrace_append hprefix tailTrace_1743256
  have hstable : (prefixWord ++ tailWord_1743256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743256).length < 2 ^ (prefixWord ++ tailWord_1743256).sum := by decide
  have hdescent : baseEnd_1743256 < baseStart_1743256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1743267 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 5]
def baseStart_1743267 : Nat := 118140960795 + 1743267 * 2 ^ 59
def prefixEnd_1743267 : Nat := 4983230072969 + 3 ^ 40 * 1743267 * 2
def baseEnd_1743267 : Nat := 397837280054016086020163

theorem tailTrace_1743267 : CollatzResearch.WordTrace tailWord_1743267 prefixEnd_1743267 397837280054016086020163 := by
  unfold tailWord_1743267
  simp only [CollatzResearch.WordTrace]
  refine ⟨63582170975448860145508055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42388113983632573430338703 63582170975448860145508055)
  ·
    refine ⟨95373256463173290218262083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63582170975448860145508055 95373256463173290218262083)
    ·
      refine ⟨143059884694759935327393125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95373256463173290218262083 143059884694759935327393125)
      ·
        refine ⟨26823728380267487873886211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143059884694759935327393125 26823728380267487873886211)
        ·
          refine ⟨40235592570401231810829317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26823728380267487873886211 40235592570401231810829317)
          ·
            refine ⟨7544173606950230964530497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40235592570401231810829317 7544173606950230964530497)
            ·
              refine ⟨5658130205212673223397873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7544173606950230964530497 5658130205212673223397873)
              ·
                refine ⟨4243597653909504917548405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5658130205212673223397873 4243597653909504917548405)
                ·
                  refine ⟨397837280054016086020163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4243597653909504917548405 397837280054016086020163)
                  ·
                    rfl

theorem cell21_1743267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_1743267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1743267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1743267 prefixEnd_1743267 := by exact prefixLift 1743267
  have htrace : WordTrace (prefixWord ++ tailWord_1743267) baseStart_1743267 baseEnd_1743267 := by
    simpa [prefixWord, tailWord_1743267, baseEnd_1743267] using wordTrace_append hprefix tailTrace_1743267
  have hstable : (prefixWord ++ tailWord_1743267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1743267).length < 2 ^ (prefixWord ++ tailWord_1743267).sum := by decide
  have hdescent : baseEnd_1743267 < baseStart_1743267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1743267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
