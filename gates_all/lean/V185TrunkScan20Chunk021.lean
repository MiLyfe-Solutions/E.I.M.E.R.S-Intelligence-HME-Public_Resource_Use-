import V185TrunkScan20Chunk020

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_127575 : List Nat := [1, 1, 3, 2, 2, 2, 5, 2, 2]
def baseStart_127575 : Nat := 118140960795 + 127575 * 2 ^ 59
def prefixEnd_127575 : Nat := 4983230072969 + 3 ^ 40 * 127575 * 2
def baseEnd_127575 : Nat := 58228706219949863045155

theorem tailTrace_127575 : CollatzResearch.WordTrace tailWord_127575 prefixEnd_127575 58228706219949863045155 := by
  unfold tailWord_127575
  simp only [CollatzResearch.WordTrace]
  refine ⟨4653042512825037920472179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3102028341883358613648119 4653042512825037920472179)
  ·
    refine ⟨6979563769237556880708269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4653042512825037920472179 6979563769237556880708269)
    ·
      refine ⟨2617336413464083830265601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6979563769237556880708269 2617336413464083830265601)
      ·
        refine ⟨1963002310098062872699201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2617336413464083830265601 1963002310098062872699201)
        ·
          refine ⟨1472251732573547154524401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1963002310098062872699201 1472251732573547154524401)
          ·
            refine ⟨1104188799430160365893301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472251732573547154524401 1104188799430160365893301)
            ·
              refine ⟨103517699946577534302497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1104188799430160365893301 103517699946577534302497)
              ·
                refine ⟨77638274959933150726873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103517699946577534302497 77638274959933150726873)
                ·
                  refine ⟨58228706219949863045155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77638274959933150726873 58228706219949863045155)
                  ·
                    rfl

theorem cell20_127575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 2].length) (baseStart_127575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127575 prefixEnd_127575 := by exact prefixLift 127575
  have htrace : WordTrace (prefixWord ++ tailWord_127575) baseStart_127575 baseEnd_127575 := by
    simpa [prefixWord, tailWord_127575, baseEnd_127575] using wordTrace_append hprefix tailTrace_127575
  have hstable : (prefixWord ++ tailWord_127575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127575).length < 2 ^ (prefixWord ++ tailWord_127575).sum := by decide
  have hdescent : baseEnd_127575 < baseStart_127575 := by decide
  rcases family_descends (prefixWord ++ tailWord_127575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127589 : List Nat := [1, 3, 1, 3, 4, 1, 1, 3, 3]
def baseStart_127589 : Nat := 118140960795 + 127589 * 2 ^ 59
def prefixEnd_127589 : Nat := 4983230072969 + 3 ^ 40 * 127589 * 2
def baseEnd_127589 : Nat := 58235096201428036578431

theorem tailTrace_127589 : CollatzResearch.WordTrace tailWord_127589 prefixEnd_127589 58235096201428036578431 := by
  unfold tailWord_127589
  simp only [CollatzResearch.WordTrace]
  refine ⟨4653553134774318311481821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3102368756516212207654547 4653553134774318311481821)
  ·
    refine ⟨1745082425540369366805683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4653553134774318311481821 1745082425540369366805683)
    ·
      refine ⟨2617623638310554050208525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745082425540369366805683 2617623638310554050208525)
      ·
        refine ⟨981608864366457768828197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2617623638310554050208525 981608864366457768828197)
        ·
          refine ⟨184051662068710831655287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 981608864366457768828197 184051662068710831655287)
          ·
            refine ⟨276077493103066247482931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184051662068710831655287 276077493103066247482931)
            ·
              refine ⟨414116239654599371224397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276077493103066247482931 414116239654599371224397)
              ·
                refine ⟨155293589870474764209149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414116239654599371224397 155293589870474764209149)
                ·
                  refine ⟨58235096201428036578431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155293589870474764209149 58235096201428036578431)
                  ·
                    rfl

theorem cell20_127589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_127589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127589 prefixEnd_127589 := by exact prefixLift 127589
  have htrace : WordTrace (prefixWord ++ tailWord_127589) baseStart_127589 baseEnd_127589 := by
    simpa [prefixWord, tailWord_127589, baseEnd_127589] using wordTrace_append hprefix tailTrace_127589
  have hstable : (prefixWord ++ tailWord_127589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127589).length < 2 ^ (prefixWord ++ tailWord_127589).sum := by decide
  have hdescent : baseEnd_127589 < baseStart_127589 := by decide
  rcases family_descends (prefixWord ++ tailWord_127589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127703 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 3]
def baseStart_127703 : Nat := 118140960795 + 127703 * 2 ^ 59
def prefixEnd_127703 : Nat := 4983230072969 + 3 ^ 40 * 127703 * 2
def baseEnd_127703 : Nat := 58287128907750306777965

theorem tailTrace_127703 : CollatzResearch.WordTrace tailWord_127703 prefixEnd_127703 58287128907750306777965 := by
  unfold tailWord_127703
  simp only [CollatzResearch.WordTrace]
  refine ⟨4657711056361315781131763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3105140704240877187421175 4657711056361315781131763)
  ·
    refine ⟨6986566584541973671697645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4657711056361315781131763 6986566584541973671697645)
    ·
      refine ⟨2619962469203240126886617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6986566584541973671697645 2619962469203240126886617)
      ·
        refine ⟨1964971851902430095164963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2619962469203240126886617 1964971851902430095164963)
        ·
          refine ⟨2947457777853645142747445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964971851902430095164963 2947457777853645142747445)
          ·
            refine ⟨276324166673779232132573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2947457777853645142747445 276324166673779232132573)
            ·
              refine ⟨103621562502667212049715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276324166673779232132573 103621562502667212049715)
              ·
                refine ⟨155432343754000818074573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103621562502667212049715 155432343754000818074573)
                ·
                  refine ⟨58287128907750306777965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155432343754000818074573 58287128907750306777965)
                  ·
                    rfl

theorem cell20_127703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 3].length) (baseStart_127703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127703 prefixEnd_127703 := by exact prefixLift 127703
  have htrace : WordTrace (prefixWord ++ tailWord_127703) baseStart_127703 baseEnd_127703 := by
    simpa [prefixWord, tailWord_127703, baseEnd_127703] using wordTrace_append hprefix tailTrace_127703
  have hstable : (prefixWord ++ tailWord_127703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127703).length < 2 ^ (prefixWord ++ tailWord_127703).sum := by decide
  have hdescent : baseEnd_127703 < baseStart_127703 := by decide
  rcases family_descends (prefixWord ++ tailWord_127703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127717 : List Nat := [1, 3, 1, 4, 1, 2, 4, 4]
def baseStart_127717 : Nat := 118140960795 + 127717 * 2 ^ 59
def prefixEnd_127717 : Nat := 4983230072969 + 3 ^ 40 * 127717 * 2
def baseEnd_127717 : Nat := 19431172963076160103747

theorem tailTrace_127717 : CollatzResearch.WordTrace tailWord_127717 prefixEnd_127717 19431172963076160103747 := by
  unfold tailWord_127717
  simp only [CollatzResearch.WordTrace]
  refine ⟨4658221678310596172141405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3105481118873730781427603 4658221678310596172141405)
  ·
    refine ⟨1746833129366473564553027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4658221678310596172141405 1746833129366473564553027)
    ·
      refine ⟨2620249694049710346829541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746833129366473564553027 2620249694049710346829541)
      ·
        refine ⟨491296817634320690030539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2620249694049710346829541 491296817634320690030539)
        ·
          refine ⟨736945226451481035045809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491296817634320690030539 736945226451481035045809)
          ·
            refine ⟨552708919838610776284357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736945226451481035045809 552708919838610776284357)
            ·
              refine ⟨103632922469739520553317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 552708919838610776284357 103632922469739520553317)
              ·
                refine ⟨19431172963076160103747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103632922469739520553317 19431172963076160103747)
                ·
                  rfl

theorem cell20_127717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 4].length) (baseStart_127717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127717 prefixEnd_127717 := by exact prefixLift 127717
  have htrace : WordTrace (prefixWord ++ tailWord_127717) baseStart_127717 baseEnd_127717 := by
    simpa [prefixWord, tailWord_127717, baseEnd_127717] using wordTrace_append hprefix tailTrace_127717
  have hstable : (prefixWord ++ tailWord_127717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127717).length < 2 ^ (prefixWord ++ tailWord_127717).sum := by decide
  have hdescent : baseEnd_127717 < baseStart_127717 := by decide
  rcases family_descends (prefixWord ++ tailWord_127717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127727 : List Nat := [1, 1, 2, 1, 5, 4, 1, 3, 2]
def baseStart_127727 : Nat := 118140960795 + 127727 * 2 ^ 59
def prefixEnd_127727 : Nat := 4983230072969 + 3 ^ 40 * 127727 * 2
def baseEnd_127727 : Nat := 58298083161712889977867

theorem tailTrace_127727 : CollatzResearch.WordTrace tailWord_127727 prefixEnd_127727 58298083161712889977867 := by
  unfold tailWord_127727
  simp only [CollatzResearch.WordTrace]
  refine ⟨4658586408274367880005435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3105724272182911920003623 4658586408274367880005435)
  ·
    refine ⟨6987879612411551820008153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4658586408274367880005435 6987879612411551820008153)
    ·
      refine ⟨5240909709308663865006115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6987879612411551820008153 5240909709308663865006115)
      ·
        refine ⟨7861364563962995797509173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5240909709308663865006115 7861364563962995797509173)
        ·
          refine ⟨737002927871530856016485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7861364563962995797509173 737002927871530856016485)
          ·
            refine ⟨138188048975912035503091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 737002927871530856016485 138188048975912035503091)
            ·
              refine ⟨207282073463868053254637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138188048975912035503091 207282073463868053254637)
              ·
                refine ⟨77730777548950519970489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207282073463868053254637 77730777548950519970489)
                ·
                  refine ⟨58298083161712889977867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77730777548950519970489 58298083161712889977867)
                  ·
                    rfl

theorem cell20_127727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 2].length) (baseStart_127727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127727 prefixEnd_127727 := by exact prefixLift 127727
  have htrace : WordTrace (prefixWord ++ tailWord_127727) baseStart_127727 baseEnd_127727 := by
    simpa [prefixWord, tailWord_127727, baseEnd_127727] using wordTrace_append hprefix tailTrace_127727
  have hstable : (prefixWord ++ tailWord_127727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127727).length < 2 ^ (prefixWord ++ tailWord_127727).sum := by decide
  have hdescent : baseEnd_127727 < baseStart_127727 := by decide
  rcases family_descends (prefixWord ++ tailWord_127727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127776 : List Nat := [2, 1, 1, 5, 1, 2, 2, 6]
def baseStart_127776 : Nat := 118140960795 + 127776 * 2 ^ 59
def prefixEnd_127776 : Nat := 4983230072969 + 3 ^ 40 * 127776 * 2
def baseEnd_127776 : Nat := 19440149365628832448111

theorem tailTrace_127776 : CollatzResearch.WordTrace tailWord_127776 prefixEnd_127776 19440149365628832448111 := by
  unfold tailWord_127776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330186792548424624269591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3106915723397899499026121 2330186792548424624269591)
  ·
    refine ⟨3495280188822636936404387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2330186792548424624269591 3495280188822636936404387)
    ·
      refine ⟨5242920283233955404606581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495280188822636936404387 5242920283233955404606581)
      ·
        refine ⟨491523776553183319181867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5242920283233955404606581 491523776553183319181867)
        ·
          refine ⟨737285664829774978772801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491523776553183319181867 737285664829774978772801)
          ·
            refine ⟨552964248622331234079601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 737285664829774978772801 552964248622331234079601)
            ·
              refine ⟨414723186466748425559701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552964248622331234079601 414723186466748425559701)
              ·
                refine ⟨19440149365628832448111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 414723186466748425559701 19440149365628832448111)
                ·
                  rfl

theorem cell20_127776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_127776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127776 prefixEnd_127776 := by exact prefixLift 127776
  have htrace : WordTrace (prefixWord ++ tailWord_127776) baseStart_127776 baseEnd_127776 := by
    simpa [prefixWord, tailWord_127776, baseEnd_127776] using wordTrace_append hprefix tailTrace_127776
  have hstable : (prefixWord ++ tailWord_127776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127776).length < 2 ^ (prefixWord ++ tailWord_127776).sum := by decide
  have hdescent : baseEnd_127776 < baseStart_127776 := by decide
  rcases family_descends (prefixWord ++ tailWord_127776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127796 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_127796 : Nat := 118140960795 + 127796 * 2 ^ 59
def prefixEnd_127796 : Nat := 4983230072969 + 3 ^ 40 * 127796 * 2
def baseEnd_127796 : Nat := 58329576641855316677585

theorem tailTrace_127796 : CollatzResearch.WordTrace tailWord_127796 prefixEnd_127796 58329576641855316677585 := by
  unfold tailWord_127796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330551522512196332133621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3107402030016261776178161 2330551522512196332133621)
  ·
    refine ⟨218489205235518406137527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2330551522512196332133621 218489205235518406137527)
    ·
      refine ⟨327733807853277609206291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218489205235518406137527 327733807853277609206291)
      ·
        refine ⟨491600711779916413809437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327733807853277609206291 491600711779916413809437)
        ·
          refine ⟨184350266917468655178539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 491600711779916413809437 184350266917468655178539)
          ·
            refine ⟨276525400376202982767809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184350266917468655178539 276525400376202982767809)
            ·
              refine ⟨207394050282152237075857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276525400376202982767809 207394050282152237075857)
              ·
                refine ⟨155545537711614177806893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207394050282152237075857 155545537711614177806893)
                ·
                  refine ⟨58329576641855316677585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155545537711614177806893 58329576641855316677585)
                  ·
                    rfl

theorem cell20_127796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_127796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127796 prefixEnd_127796 := by exact prefixLift 127796
  have htrace : WordTrace (prefixWord ++ tailWord_127796) baseStart_127796 baseEnd_127796 := by
    simpa [prefixWord, tailWord_127796, baseEnd_127796] using wordTrace_append hprefix tailTrace_127796
  have hstable : (prefixWord ++ tailWord_127796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127796).length < 2 ^ (prefixWord ++ tailWord_127796).sum := by decide
  have hdescent : baseEnd_127796 < baseStart_127796 := by decide
  rcases family_descends (prefixWord ++ tailWord_127796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127800 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_127800 : Nat := 118140960795 + 127800 * 2 ^ 59
def prefixEnd_127800 : Nat := 4983230072969 + 3 ^ 40 * 127800 * 2
def baseEnd_127800 : Nat := 58331402350849080544235

theorem tailTrace_127800 : CollatzResearch.WordTrace tailWord_127800 prefixEnd_127800 58331402350849080544235 := by
  unfold tailWord_127800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330624468504950673706427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3107499291339934231608569 2330624468504950673706427)
  ·
    refine ⟨3495936702757426010559641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2330624468504950673706427 3495936702757426010559641)
    ·
      refine ⟨2621952527068069507919731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3495936702757426010559641 2621952527068069507919731)
      ·
        refine ⟨3932928790602104261879597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621952527068069507919731 3932928790602104261879597)
        ·
          refine ⟨1474848296475789098204849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3932928790602104261879597 1474848296475789098204849)
          ·
            refine ⟨1106136222356841823653637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1474848296475789098204849 1106136222356841823653637)
            ·
              refine ⟨207400541691907841935057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1106136222356841823653637 207400541691907841935057)
              ·
                refine ⟨155550406268930881451293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207400541691907841935057 155550406268930881451293)
                ·
                  refine ⟨58331402350849080544235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155550406268930881451293 58331402350849080544235)
                  ·
                    rfl

theorem cell20_127800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_127800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127800 prefixEnd_127800 := by exact prefixLift 127800
  have htrace : WordTrace (prefixWord ++ tailWord_127800) baseStart_127800 baseEnd_127800 := by
    simpa [prefixWord, tailWord_127800, baseEnd_127800] using wordTrace_append hprefix tailTrace_127800
  have hstable : (prefixWord ++ tailWord_127800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127800).length < 2 ^ (prefixWord ++ tailWord_127800).sum := by decide
  have hdescent : baseEnd_127800 < baseStart_127800 := by decide
  rcases family_descends (prefixWord ++ tailWord_127800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127831 : List Nat := [1, 1, 3, 2, 4, 2, 3, 4]
def baseStart_127831 : Nat := 118140960795 + 127831 * 2 ^ 59
def prefixEnd_127831 : Nat := 4983230072969 + 3 ^ 40 * 127831 * 2
def baseEnd_127831 : Nat := 19448517198516916836925

theorem tailTrace_127831 : CollatzResearch.WordTrace tailWord_127831 prefixEnd_127831 19448517198516916836925 := by
  unfold tailWord_127831
  simp only [CollatzResearch.WordTrace]
  refine ⟨4662379599897593641791347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3108253066598395761194231 4662379599897593641791347)
  ·
    refine ⟨6993569399846390462687021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4662379599897593641791347 6993569399846390462687021)
    ·
      refine ⟨2622588524942396423507633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6993569399846390462687021 2622588524942396423507633)
      ·
        refine ⟨1966941393706797317630725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2622588524942396423507633 1966941393706797317630725)
        ·
          refine ⟨368801511320024497055761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1966941393706797317630725 368801511320024497055761)
          ·
            refine ⟨276601133490018372791821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368801511320024497055761 276601133490018372791821)
            ·
              refine ⟨103725425058756889796933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276601133490018372791821 103725425058756889796933)
              ·
                refine ⟨19448517198516916836925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103725425058756889796933 19448517198516916836925)
                ·
                  rfl

theorem cell20_127831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 4].length) (baseStart_127831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127831 prefixEnd_127831 := by exact prefixLift 127831
  have htrace : WordTrace (prefixWord ++ tailWord_127831) baseStart_127831 baseEnd_127831 := by
    simpa [prefixWord, tailWord_127831, baseEnd_127831] using wordTrace_append hprefix tailTrace_127831
  have hstable : (prefixWord ++ tailWord_127831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127831).length < 2 ^ (prefixWord ++ tailWord_127831).sum := by decide
  have hdescent : baseEnd_127831 < baseStart_127831 := by decide
  rcases family_descends (prefixWord ++ tailWord_127831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127862 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_127862 : Nat := 118140960795 + 127862 * 2 ^ 59
def prefixEnd_127862 : Nat := 4983230072969 + 3 ^ 40 * 127862 * 2
def baseEnd_127862 : Nat := 58359700840252420477315

theorem tailTrace_127862 : CollatzResearch.WordTrace tailWord_127862 prefixEnd_127862 58359700840252420477315 := by
  unfold tailWord_127862
  simp only [CollatzResearch.WordTrace]
  refine ⟨291469391424080371010615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3109006841856857290779893 291469391424080371010615)
  ·
    refine ⟨437204087136120556515923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291469391424080371010615 437204087136120556515923)
    ·
      refine ⟨655806130704180834773885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437204087136120556515923 655806130704180834773885)
      ·
        refine ⟨245927299014067813040207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 655806130704180834773885 245927299014067813040207)
        ·
          refine ⟨368890948521101719560311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245927299014067813040207 368890948521101719560311)
          ·
            refine ⟨553336422781652579340467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368890948521101719560311 553336422781652579340467)
            ·
              refine ⟨830004634172478869010701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553336422781652579340467 830004634172478869010701)
              ·
                refine ⟨311251737814679575879013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830004634172478869010701 311251737814679575879013)
                ·
                  refine ⟨58359700840252420477315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311251737814679575879013 58359700840252420477315)
                  ·
                    rfl

theorem cell20_127862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_127862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127862 prefixEnd_127862 := by exact prefixLift 127862
  have htrace : WordTrace (prefixWord ++ tailWord_127862) baseStart_127862 baseEnd_127862 := by
    simpa [prefixWord, tailWord_127862, baseEnd_127862] using wordTrace_append hprefix tailTrace_127862
  have hstable : (prefixWord ++ tailWord_127862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127862).length < 2 ^ (prefixWord ++ tailWord_127862).sum := by decide
  have hdescent : baseEnd_127862 < baseStart_127862 := by decide
  rcases family_descends (prefixWord ++ tailWord_127862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127904 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_127904 : Nat := 118140960795 + 127904 * 2 ^ 59
def prefixEnd_127904 : Nat := 4983230072969 + 3 ^ 40 * 127904 * 2
def baseEnd_127904 : Nat := 58378870784686941077143

theorem tailTrace_127904 : CollatzResearch.WordTrace tailWord_127904 prefixEnd_127904 58378870784686941077143 := by
  unfold tailWord_127904
  simp only [CollatzResearch.WordTrace]
  refine ⟨2332521064316563554599383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3110028085755418072799177 2332521064316563554599383)
  ·
    refine ⟨3498781596474845331899075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2332521064316563554599383 3498781596474845331899075)
    ·
      refine ⟨5248172394712267997848613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3498781596474845331899075 5248172394712267997848613)
      ·
        refine ⟨984032324008550249596615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5248172394712267997848613 984032324008550249596615)
        ·
          refine ⟨1476048486012825374394923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984032324008550249596615 1476048486012825374394923)
          ·
            refine ⟨2214072729019238061592385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476048486012825374394923 2214072729019238061592385)
            ·
              refine ⟨1660554546764428546194289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2214072729019238061592385 1660554546764428546194289)
              ·
                refine ⟨1245415910073321409645717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660554546764428546194289 1245415910073321409645717)
                ·
                  refine ⟨58378870784686941077143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1245415910073321409645717 58378870784686941077143)
                  ·
                    rfl

theorem cell20_127904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_127904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127904 prefixEnd_127904 := by exact prefixLift 127904
  have htrace : WordTrace (prefixWord ++ tailWord_127904) baseStart_127904 baseEnd_127904 := by
    simpa [prefixWord, tailWord_127904, baseEnd_127904] using wordTrace_append hprefix tailTrace_127904
  have hstable : (prefixWord ++ tailWord_127904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127904).length < 2 ^ (prefixWord ++ tailWord_127904).sum := by decide
  have hdescent : baseEnd_127904 < baseStart_127904 := by decide
  rcases family_descends (prefixWord ++ tailWord_127904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127924 : List Nat := [2, 5, 2, 1, 1, 2, 2, 5]
def baseStart_127924 : Nat := 118140960795 + 127924 * 2 ^ 59
def prefixEnd_127924 : Nat := 4983230072969 + 3 ^ 40 * 127924 * 2
def baseEnd_127924 : Nat := 19462666443218586803465

theorem tailTrace_127924 : CollatzResearch.WordTrace tailWord_127924 prefixEnd_127924 19462666443218586803465 := by
  unfold tailWord_127924
  simp only [CollatzResearch.WordTrace]
  refine ⟨2332885794280335262463413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3110514392373780349951217 2332885794280335262463413)
  ·
    refine ⟨218708043213781430855945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2332885794280335262463413 218708043213781430855945)
    ·
      refine ⟨164031032410336073141959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218708043213781430855945 164031032410336073141959)
      ·
        refine ⟨246046548615504109712939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164031032410336073141959 246046548615504109712939)
        ·
          refine ⟨369069822923256164569409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246046548615504109712939 369069822923256164569409)
          ·
            refine ⟨276802367192442123427057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369069822923256164569409 276802367192442123427057)
            ·
              refine ⟨207601775394331592570293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276802367192442123427057 207601775394331592570293)
              ·
                refine ⟨19462666443218586803465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207601775394331592570293 19462666443218586803465)
                ·
                  rfl

theorem cell20_127924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_127924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127924 prefixEnd_127924 := by exact prefixLift 127924
  have htrace : WordTrace (prefixWord ++ tailWord_127924) baseStart_127924 baseEnd_127924 := by
    simpa [prefixWord, tailWord_127924, baseEnd_127924] using wordTrace_append hprefix tailTrace_127924
  have hstable : (prefixWord ++ tailWord_127924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127924).length < 2 ^ (prefixWord ++ tailWord_127924).sum := by decide
  have hdescent : baseEnd_127924 < baseStart_127924 := by decide
  rcases family_descends (prefixWord ++ tailWord_127924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127928 : List Nat := [2, 1, 2, 1, 2, 5, 2, 5]
def baseStart_127928 : Nat := 118140960795 + 127928 * 2 ^ 59
def prefixEnd_127928 : Nat := 4983230072969 + 3 ^ 40 * 127928 * 2
def baseEnd_127928 : Nat := 19463275012883174759015

theorem tailTrace_127928 : CollatzResearch.WordTrace tailWord_127928 prefixEnd_127928 19463275012883174759015 := by
  unfold tailWord_127928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2332958740273089604036219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3110611653697452805381625 2332958740273089604036219)
  ·
    refine ⟨3499438110409634406054329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2332958740273089604036219 3499438110409634406054329)
    ·
      refine ⟨2624578582807225804540747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3499438110409634406054329 2624578582807225804540747)
      ·
        refine ⟨3936867874210838706811121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624578582807225804540747 3936867874210838706811121)
        ·
          refine ⟨2952650905658129030108341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3936867874210838706811121 2952650905658129030108341)
          ·
            refine ⟨276811022405449596572657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2952650905658129030108341 276811022405449596572657)
            ·
              refine ⟨207608266804087197429493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276811022405449596572657 207608266804087197429493)
              ·
                refine ⟨19463275012883174759015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207608266804087197429493 19463275012883174759015)
                ·
                  rfl

theorem cell20_127928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_127928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_127928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_127928 prefixEnd_127928 := by exact prefixLift 127928
  have htrace : WordTrace (prefixWord ++ tailWord_127928) baseStart_127928 baseEnd_127928 := by
    simpa [prefixWord, tailWord_127928, baseEnd_127928] using wordTrace_append hprefix tailTrace_127928
  have hstable : (prefixWord ++ tailWord_127928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127928).length < 2 ^ (prefixWord ++ tailWord_127928).sum := by decide
  have hdescent : baseEnd_127928 < baseStart_127928 := by decide
  rcases family_descends (prefixWord ++ tailWord_127928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128014 : List Nat := [4, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_128014 : Nat := 118140960795 + 128014 * 2 ^ 59
def prefixEnd_128014 : Nat := 4983230072969 + 3 ^ 40 * 128014 * 2
def baseEnd_128014 : Nat := 58429077782015447410027

theorem tailTrace_128014 : CollatzResearch.WordTrace tailWord_128014 prefixEnd_128014 58429077782015447410027 := by
  unfold tailWord_128014
  simp only [CollatzResearch.WordTrace]
  refine ⟨583631769779326986962887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3112702772156410597135397 583631769779326986962887)
  ·
    refine ⟨875447654668990480444331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 583631769779326986962887 875447654668990480444331)
    ·
      refine ⟨1313171482003485720666497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 875447654668990480444331 1313171482003485720666497)
      ·
        refine ⟨984878611502614290499873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313171482003485720666497 984878611502614290499873)
        ·
          refine ⟨738658958626960717874905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984878611502614290499873 738658958626960717874905)
          ·
            refine ⟨553994218970220538406179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 738658958626960717874905 553994218970220538406179)
            ·
              refine ⟨830991328455330807609269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553994218970220538406179 830991328455330807609269)
              ·
                refine ⟨77905437042687263213369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 830991328455330807609269 77905437042687263213369)
                ·
                  refine ⟨58429077782015447410027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77905437042687263213369 58429077782015447410027)
                  ·
                    rfl

theorem cell20_128014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_128014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128014 prefixEnd_128014 := by exact prefixLift 128014
  have htrace : WordTrace (prefixWord ++ tailWord_128014) baseStart_128014 baseEnd_128014 := by
    simpa [prefixWord, tailWord_128014, baseEnd_128014] using wordTrace_append hprefix tailTrace_128014
  have hstable : (prefixWord ++ tailWord_128014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128014).length < 2 ^ (prefixWord ++ tailWord_128014).sum := by decide
  have hdescent : baseEnd_128014 < baseStart_128014 := by decide
  rcases family_descends (prefixWord ++ tailWord_128014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128028 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_128028 : Nat := 118140960795 + 128028 * 2 ^ 59
def prefixEnd_128028 : Nat := 4983230072969 + 3 ^ 40 * 128028 * 2
def baseEnd_128028 : Nat := 58435467763493620943303

theorem tailTrace_128028 : CollatzResearch.WordTrace tailWord_128028 prefixEnd_128028 58435467763493620943303 := by
  unfold tailWord_128028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334782390091948143356369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3113043186789264191141825 2334782390091948143356369)
  ·
    refine ⟨1751086792568961107517277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2334782390091948143356369 1751086792568961107517277)
    ·
      refine ⟨656657547213360415318979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1751086792568961107517277 656657547213360415318979)
      ·
        refine ⟨984986320820040622978469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 656657547213360415318979 984986320820040622978469)
        ·
          refine ⟨184684935153757616808463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 984986320820040622978469 184684935153757616808463)
          ·
            refine ⟨277027402730636425212695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184684935153757616808463 277027402730636425212695)
            ·
              refine ⟨415541104095954637819043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277027402730636425212695 415541104095954637819043)
              ·
                refine ⟨623311656143931956728565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415541104095954637819043 623311656143931956728565)
                ·
                  refine ⟨58435467763493620943303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 623311656143931956728565 58435467763493620943303)
                  ·
                    rfl

theorem cell20_128028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_128028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128028 prefixEnd_128028 := by exact prefixLift 128028
  have htrace : WordTrace (prefixWord ++ tailWord_128028) baseStart_128028 baseEnd_128028 := by
    simpa [prefixWord, tailWord_128028, baseEnd_128028] using wordTrace_append hprefix tailTrace_128028
  have hstable : (prefixWord ++ tailWord_128028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128028).length < 2 ^ (prefixWord ++ tailWord_128028).sum := by decide
  have hdescent : baseEnd_128028 < baseStart_128028 := by decide
  rcases family_descends (prefixWord ++ tailWord_128028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128035 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_128035 : Nat := 118140960795 + 128035 * 2 ^ 59
def prefixEnd_128035 : Nat := 4983230072969 + 3 ^ 40 * 128035 * 2
def baseEnd_128035 : Nat := 58438662754232707709941

theorem tailTrace_128035 : CollatzResearch.WordTrace tailWord_128035 prefixEnd_128035 58438662754232707709941 := by
  unfold tailWord_128035
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669820091158536482217559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3113213394105690988145039 4669820091158536482217559)
  ·
    refine ⟨7004730136737804723326339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4669820091158536482217559 7004730136737804723326339)
    ·
      refine ⟨10507095205106707084989509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7004730136737804723326339 10507095205106707084989509)
      ·
        refine ⟨1970080350957507578435533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10507095205106707084989509 1970080350957507578435533)
        ·
          refine ⟨738780131609065341913325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1970080350957507578435533 738780131609065341913325)
          ·
            refine ⟨277042549353399503217497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 738780131609065341913325 277042549353399503217497)
            ·
              refine ⟨207781912015049627413123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277042549353399503217497 207781912015049627413123)
              ·
                refine ⟨311672868022574441119685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207781912015049627413123 311672868022574441119685)
                ·
                  refine ⟨58438662754232707709941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311672868022574441119685 58438662754232707709941)
                  ·
                    rfl

theorem cell20_128035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_128035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128035 prefixEnd_128035 := by exact prefixLift 128035
  have htrace : WordTrace (prefixWord ++ tailWord_128035) baseStart_128035 baseEnd_128035 := by
    simpa [prefixWord, tailWord_128035, baseEnd_128035] using wordTrace_append hprefix tailTrace_128035
  have hstable : (prefixWord ++ tailWord_128035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128035).length < 2 ^ (prefixWord ++ tailWord_128035).sum := by decide
  have hdescent : baseEnd_128035 < baseStart_128035 := by decide
  rcases family_descends (prefixWord ++ tailWord_128035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128052 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_128052 : Nat := 118140960795 + 128052 * 2 ^ 59
def prefixEnd_128052 : Nat := 4983230072969 + 3 ^ 40 * 128052 * 2
def baseEnd_128052 : Nat := 58446422017456204143205

theorem tailTrace_128052 : CollatzResearch.WordTrace tailWord_128052 prefixEnd_128052 58446422017456204143205 := by
  unfold tailWord_128052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335220066048474192793205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3113626754731298923724273 2335220066048474192793205)
  ·
    refine ⟨218926881192044455574363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2335220066048474192793205 218926881192044455574363)
    ·
      refine ⟨328390321788066683361545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218926881192044455574363 328390321788066683361545)
      ·
        refine ⟨246292741341050012521159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328390321788066683361545 246292741341050012521159)
        ·
          refine ⟨369439112011575018781739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246292741341050012521159 369439112011575018781739)
          ·
            refine ⟨554158668017362528172609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369439112011575018781739 554158668017362528172609)
            ·
              refine ⟨415619001013021896129457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554158668017362528172609 415619001013021896129457)
              ·
                refine ⟨311714250759766422097093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415619001013021896129457 311714250759766422097093)
                ·
                  refine ⟨58446422017456204143205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311714250759766422097093 58446422017456204143205)
                  ·
                    rfl

theorem cell20_128052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_128052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128052 prefixEnd_128052 := by exact prefixLift 128052
  have htrace : WordTrace (prefixWord ++ tailWord_128052) baseStart_128052 baseEnd_128052 := by
    simpa [prefixWord, tailWord_128052, baseEnd_128052] using wordTrace_append hprefix tailTrace_128052
  have hstable : (prefixWord ++ tailWord_128052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128052).length < 2 ^ (prefixWord ++ tailWord_128052).sum := by decide
  have hdescent : baseEnd_128052 < baseStart_128052 := by decide
  rcases family_descends (prefixWord ++ tailWord_128052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128073 : List Nat := [1, 2, 1, 1, 2, 2, 2, 7, 2]
def baseStart_128073 : Nat := 118140960795 + 128073 * 2 ^ 59
def prefixEnd_128073 : Nat := 4983230072969 + 3 ^ 40 * 128073 * 2
def baseEnd_128073 : Nat := 58456006989673464443119

theorem tailTrace_128073 : CollatzResearch.WordTrace tailWord_128073 prefixEnd_128073 58456006989673464443119 := by
  unfold tailWord_128073
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671206065020868972100873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3114137376680579314733915 4671206065020868972100873)
  ·
    refine ⟨3503404548765651729075655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4671206065020868972100873 3503404548765651729075655)
    ·
      refine ⟨5255106823148477593613483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503404548765651729075655 5255106823148477593613483)
      ·
        refine ⟨7882660234722716390420225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5255106823148477593613483 7882660234722716390420225)
        ·
          refine ⟨5911995176042037292815169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7882660234722716390420225 5911995176042037292815169)
          ·
            refine ⟨4433996382031527969611377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5911995176042037292815169 4433996382031527969611377)
            ·
              refine ⟨3325497286523645977208533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4433996382031527969611377 3325497286523645977208533)
              ·
                refine ⟨77941342652897952590825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3325497286523645977208533 77941342652897952590825)
                ·
                  refine ⟨58456006989673464443119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77941342652897952590825 58456006989673464443119)
                  ·
                    rfl

theorem cell20_128073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_128073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128073 prefixEnd_128073 := by exact prefixLift 128073
  have htrace : WordTrace (prefixWord ++ tailWord_128073) baseStart_128073 baseEnd_128073 := by
    simpa [prefixWord, tailWord_128073, baseEnd_128073] using wordTrace_append hprefix tailTrace_128073
  have hstable : (prefixWord ++ tailWord_128073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128073).length < 2 ^ (prefixWord ++ tailWord_128073).sum := by decide
  have hdescent : baseEnd_128073 < baseStart_128073 := by decide
  rcases family_descends (prefixWord ++ tailWord_128073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128086 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_128086 : Nat := 118140960795 + 128086 * 2 ^ 59
def prefixEnd_128086 : Nat := 4983230072969 + 3 ^ 40 * 128086 * 2
def baseEnd_128086 : Nat := 58461940543903197009733

theorem tailTrace_128086 : CollatzResearch.WordTrace tailWord_128086 prefixEnd_128086 58461940543903197009733 := by
  unfold tailWord_128086
  simp only [CollatzResearch.WordTrace]
  refine ⟨291980013373360762020257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3114453475982514794882741 291980013373360762020257)
  ·
    refine ⟨218985010030020571515193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291980013373360762020257 218985010030020571515193)
    ·
      refine ⟨164238757522515428636395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218985010030020571515193 164238757522515428636395)
      ·
        refine ⟨246358136283773142954593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164238757522515428636395 246358136283773142954593)
        ·
          refine ⟨184768602212829857215945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246358136283773142954593 184768602212829857215945)
          ·
            refine ⟨138576451659622392911959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184768602212829857215945 138576451659622392911959)
            ·
              refine ⟨207864677489433589367939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138576451659622392911959 207864677489433589367939)
              ·
                refine ⟨311797016234150384051909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207864677489433589367939 311797016234150384051909)
                ·
                  refine ⟨58461940543903197009733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 311797016234150384051909 58461940543903197009733)
                  ·
                    rfl

theorem cell20_128086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_128086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128086 prefixEnd_128086 := by exact prefixLift 128086
  have htrace : WordTrace (prefixWord ++ tailWord_128086) baseStart_128086 baseEnd_128086 := by
    simpa [prefixWord, tailWord_128086, baseEnd_128086] using wordTrace_append hprefix tailTrace_128086
  have hstable : (prefixWord ++ tailWord_128086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128086).length < 2 ^ (prefixWord ++ tailWord_128086).sum := by decide
  have hdescent : baseEnd_128086 < baseStart_128086 := by decide
  rcases family_descends (prefixWord ++ tailWord_128086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128087 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 3]
def baseStart_128087 : Nat := 118140960795 + 128087 * 2 ^ 59
def prefixEnd_128087 : Nat := 4983230072969 + 3 ^ 40 * 128087 * 2
def baseEnd_128087 : Nat := 58462396971151637976395

theorem tailTrace_128087 : CollatzResearch.WordTrace tailWord_128087 prefixEnd_128087 58462396971151637976395 := by
  unfold tailWord_128087
  simp only [CollatzResearch.WordTrace]
  refine ⟨4671716686970149363110515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3114477791313432908740343 4671716686970149363110515)
  ·
    refine ⟨7007575030455224044665773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4671716686970149363110515 7007575030455224044665773)
    ·
      refine ⟨2627840636420709016749665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7007575030455224044665773 2627840636420709016749665)
      ·
        refine ⟨1970880477315531762562249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2627840636420709016749665 1970880477315531762562249)
        ·
          refine ⟨1478160357986648821921687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1970880477315531762562249 1478160357986648821921687)
          ·
            refine ⟨2217240536979973232882531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478160357986648821921687 2217240536979973232882531)
            ·
              refine ⟨3325860805469959849323797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217240536979973232882531 3325860805469959849323797)
              ·
                refine ⟨155899725256404367937053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3325860805469959849323797 155899725256404367937053)
                ·
                  refine ⟨58462396971151637976395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155899725256404367937053 58462396971151637976395)
                  ·
                    rfl

theorem cell20_128087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_128087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128087 prefixEnd_128087 := by exact prefixLift 128087
  have htrace : WordTrace (prefixWord ++ tailWord_128087) baseStart_128087 baseEnd_128087 := by
    simpa [prefixWord, tailWord_128087, baseEnd_128087] using wordTrace_append hprefix tailTrace_128087
  have hstable : (prefixWord ++ tailWord_128087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128087).length < 2 ^ (prefixWord ++ tailWord_128087).sum := by decide
  have hdescent : baseEnd_128087 < baseStart_128087 := by decide
  rcases family_descends (prefixWord ++ tailWord_128087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128118 : List Nat := [5, 1, 1, 2, 1, 1, 1, 8]
def baseStart_128118 : Nat := 118140960795 + 128118 * 2 ^ 59
def prefixEnd_128118 : Nat := 4983230072969 + 3 ^ 40 * 128118 * 2
def baseEnd_128118 : Nat := 19492182071951102647645

theorem tailTrace_128118 : CollatzResearch.WordTrace tailWord_128118 prefixEnd_128118 19492182071951102647645 := by
  unfold tailWord_128118
  simp only [CollatzResearch.WordTrace]
  refine ⟨292052959366115103593063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3115231566571894438326005 292052959366115103593063)
  ·
    refine ⟨438079439049172655389595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292052959366115103593063 438079439049172655389595)
    ·
      refine ⟨657119158573758983084393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438079439049172655389595 657119158573758983084393)
      ·
        refine ⟨492839368930319237313295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657119158573758983084393 492839368930319237313295)
        ·
          refine ⟨739259053395478855969943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492839368930319237313295 739259053395478855969943)
          ·
            refine ⟨1108888580093218283954915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739259053395478855969943 1108888580093218283954915)
            ·
              refine ⟨1663332870139827425932373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108888580093218283954915 1663332870139827425932373)
              ·
                refine ⟨19492182071951102647645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1663332870139827425932373 19492182071951102647645)
                ·
                  rfl

theorem cell20_128118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_128118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128118 prefixEnd_128118 := by exact prefixLift 128118
  have htrace : WordTrace (prefixWord ++ tailWord_128118) baseStart_128118 baseEnd_128118 := by
    simpa [prefixWord, tailWord_128118, baseEnd_128118] using wordTrace_append hprefix tailTrace_128118
  have hstable : (prefixWord ++ tailWord_128118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128118).length < 2 ^ (prefixWord ++ tailWord_128118).sum := by decide
  have hdescent : baseEnd_128118 < baseStart_128118 := by decide
  rcases family_descends (prefixWord ++ tailWord_128118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128142 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_128142 : Nat := 118140960795 + 128142 * 2 ^ 59
def prefixEnd_128142 : Nat := 4983230072969 + 3 ^ 40 * 128142 * 2
def baseEnd_128142 : Nat := 58487500469815891142837

theorem tailTrace_128142 : CollatzResearch.WordTrace tailWord_128142 prefixEnd_128142 58487500469815891142837 := by
  unfold tailWord_128142
  simp only [CollatzResearch.WordTrace]
  refine ⟨584215337721361719545335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3115815134513929170908453 584215337721361719545335)
  ·
    refine ⟨876323006582042579318003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 584215337721361719545335 876323006582042579318003)
    ·
      refine ⟨1314484509873063868977005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 876323006582042579318003 1314484509873063868977005)
      ·
        refine ⟨492931691202398950866377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1314484509873063868977005 492931691202398950866377)
        ·
          refine ⟨369698768401799213149783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492931691202398950866377 369698768401799213149783)
          ·
            refine ⟨554548152602698819724675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369698768401799213149783 554548152602698819724675)
            ·
              refine ⟨831822228904048229587013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 554548152602698819724675 831822228904048229587013)
              ·
                refine ⟨155966667919509043047565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831822228904048229587013 155966667919509043047565)
                ·
                  refine ⟨58487500469815891142837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155966667919509043047565 58487500469815891142837)
                  ·
                    rfl

theorem cell20_128142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_128142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128142 prefixEnd_128142 := by exact prefixLift 128142
  have htrace : WordTrace (prefixWord ++ tailWord_128142) baseStart_128142 baseEnd_128142 := by
    simpa [prefixWord, tailWord_128142, baseEnd_128142] using wordTrace_append hprefix tailTrace_128142
  have hstable : (prefixWord ++ tailWord_128142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128142).length < 2 ^ (prefixWord ++ tailWord_128142).sum := by decide
  have hdescent : baseEnd_128142 < baseStart_128142 := by decide
  rcases family_descends (prefixWord ++ tailWord_128142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128156 : List Nat := [2, 2, 3, 2, 1, 2, 3, 5]
def baseStart_128156 : Nat := 118140960795 + 128156 * 2 ^ 59
def prefixEnd_128156 : Nat := 4983230072969 + 3 ^ 40 * 128156 * 2
def baseEnd_128156 : Nat := 19497963483764688225371

theorem tailTrace_128156 : CollatzResearch.WordTrace tailWord_128156 prefixEnd_128156 19497963483764688225371 := by
  unfold tailWord_128156
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337116661860087073686161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3116155549146782764914881 2337116661860087073686161)
  ·
    refine ⟨1752837496395065305264621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2337116661860087073686161 1752837496395065305264621)
    ·
      refine ⟨657314061148149489474233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1752837496395065305264621 657314061148149489474233)
      ·
        refine ⟨492985545861112117105675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 657314061148149489474233 492985545861112117105675)
        ·
          refine ⟨739478318791668175658513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492985545861112117105675 739478318791668175658513)
          ·
            refine ⟨554608739093751131743885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739478318791668175658513 554608739093751131743885)
            ·
              refine ⟨207978277160156674403957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554608739093751131743885 207978277160156674403957)
              ·
                refine ⟨19497963483764688225371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207978277160156674403957 19497963483764688225371)
                ·
                  rfl

theorem cell20_128156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_128156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128156 prefixEnd_128156 := by exact prefixLift 128156
  have htrace : WordTrace (prefixWord ++ tailWord_128156) baseStart_128156 baseEnd_128156 := by
    simpa [prefixWord, tailWord_128156, baseEnd_128156] using wordTrace_append hprefix tailTrace_128156
  have hstable : (prefixWord ++ tailWord_128156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128156).length < 2 ^ (prefixWord ++ tailWord_128156).sum := by decide
  have hdescent : baseEnd_128156 < baseStart_128156 := by decide
  rcases family_descends (prefixWord ++ tailWord_128156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128270 : List Nat := [4, 1, 1, 2, 1, 4, 2, 5]
def baseStart_128270 : Nat := 118140960795 + 128270 * 2 ^ 59
def prefixEnd_128270 : Nat := 4983230072969 + 3 ^ 40 * 128270 * 2
def baseEnd_128270 : Nat := 19515307719205444958549

theorem tailTrace_128270 : CollatzResearch.WordTrace tailWord_128270 prefixEnd_128270 19515307719205444958549 := by
  unfold tailWord_128270
  simp only [CollatzResearch.WordTrace]
  refine ⟨584798905663396452127783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3118927496871447744681509 584798905663396452127783)
  ·
    refine ⟨877198358495094678191675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 584798905663396452127783 877198358495094678191675)
    ·
      refine ⟨1315797537742642017287513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877198358495094678191675 1315797537742642017287513)
      ·
        refine ⟨986848153306981512965635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1315797537742642017287513 986848153306981512965635)
        ·
          refine ⟨1480272229960472269448453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986848153306981512965635 1480272229960472269448453)
          ·
            refine ⟨277551043117588550521585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1480272229960472269448453 277551043117588550521585)
            ·
              refine ⟨208163282338191412891189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277551043117588550521585 208163282338191412891189)
              ·
                refine ⟨19515307719205444958549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208163282338191412891189 19515307719205444958549)
                ·
                  rfl

theorem cell20_128270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_128270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128270 prefixEnd_128270 := by exact prefixLift 128270
  have htrace : WordTrace (prefixWord ++ tailWord_128270) baseStart_128270 baseEnd_128270 := by
    simpa [prefixWord, tailWord_128270, baseEnd_128270] using wordTrace_append hprefix tailTrace_128270
  have hstable : (prefixWord ++ tailWord_128270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128270).length < 2 ^ (prefixWord ++ tailWord_128270).sum := by decide
  have hdescent : baseEnd_128270 < baseStart_128270 := by decide
  rcases family_descends (prefixWord ++ tailWord_128270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128284 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_128284 : Nat := 118140960795 + 128284 * 2 ^ 59
def prefixEnd_128284 : Nat := 4983230072969 + 3 ^ 40 * 128284 * 2
def baseEnd_128284 : Nat := 58552313139094508408923

theorem tailTrace_128284 : CollatzResearch.WordTrace tailWord_128284 prefixEnd_128284 58552313139094508408923 := by
  unfold tailWord_128284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2339450933628226004015953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3119267911504301338687937 2339450933628226004015953)
  ·
    refine ⟨1754588200221169503011965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2339450933628226004015953 1754588200221169503011965)
    ·
      refine ⟨657970575082938563629487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1754588200221169503011965 657970575082938563629487)
      ·
        refine ⟨986955862624407845444231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657970575082938563629487 986955862624407845444231)
        ·
          refine ⟨1480433793936611768166347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 986955862624407845444231 1480433793936611768166347)
          ·
            refine ⟨2220650690904917652249521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480433793936611768166347 2220650690904917652249521)
            ·
              refine ⟨1665488018178688239187141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220650690904917652249521 1665488018178688239187141)
              ·
                refine ⟨312279003408504044847589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1665488018178688239187141 312279003408504044847589)
                ·
                  refine ⟨58552313139094508408923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312279003408504044847589 58552313139094508408923)
                  ·
                    rfl

theorem cell20_128284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_128284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128284 prefixEnd_128284 := by exact prefixLift 128284
  have htrace : WordTrace (prefixWord ++ tailWord_128284) baseStart_128284 baseEnd_128284 := by
    simpa [prefixWord, tailWord_128284, baseEnd_128284] using wordTrace_append hprefix tailTrace_128284
  have hstable : (prefixWord ++ tailWord_128284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128284).length < 2 ^ (prefixWord ++ tailWord_128284).sum := by decide
  have hdescent : baseEnd_128284 < baseStart_128284 := by decide
  rcases family_descends (prefixWord ++ tailWord_128284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128291 : List Nat := [1, 1, 1, 4, 2, 3, 2, 6]
def baseStart_128291 : Nat := 118140960795 + 128291 * 2 ^ 59
def prefixEnd_128291 : Nat := 4983230072969 + 3 ^ 40 * 128291 * 2
def baseEnd_128291 : Nat := 19518502709944531725187

theorem tailTrace_128291 : CollatzResearch.WordTrace tailWord_128291 prefixEnd_128291 19518502709944531725187 := by
  unfold tailWord_128291
  simp only [CollatzResearch.WordTrace]
  refine ⟨4679157178231092203536727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3119438118820728135691151 4679157178231092203536727)
  ·
    refine ⟨7018735767346638305305091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4679157178231092203536727 7018735767346638305305091)
    ·
      refine ⟨10528103651019957457957637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7018735767346638305305091 10528103651019957457957637)
      ·
        refine ⟨1974019434566242023367057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10528103651019957457957637 1974019434566242023367057)
        ·
          refine ⟨1480514575924681517525293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974019434566242023367057 1480514575924681517525293)
          ·
            refine ⟨555192965971755569071985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1480514575924681517525293 555192965971755569071985)
            ·
              refine ⟨416394724478816676803989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555192965971755569071985 416394724478816676803989)
              ·
                refine ⟨19518502709944531725187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 416394724478816676803989 19518502709944531725187)
                ·
                  rfl

theorem cell20_128291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_128291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128291 prefixEnd_128291 := by exact prefixLift 128291
  have htrace : WordTrace (prefixWord ++ tailWord_128291) baseStart_128291 baseEnd_128291 := by
    simpa [prefixWord, tailWord_128291, baseEnd_128291] using wordTrace_append hprefix tailTrace_128291
  have hstable : (prefixWord ++ tailWord_128291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128291).length < 2 ^ (prefixWord ++ tailWord_128291).sum := by decide
  have hdescent : baseEnd_128291 < baseStart_128291 := by decide
  rcases family_descends (prefixWord ++ tailWord_128291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128310 : List Nat := [5, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_128310 : Nat := 118140960795 + 128310 * 2 ^ 59
def prefixEnd_128310 : Nat := 4983230072969 + 3 ^ 40 * 128310 * 2
def baseEnd_128310 : Nat := 58564180247553973542151

theorem tailTrace_128310 : CollatzResearch.WordTrace tailWord_128310 prefixEnd_128310 58564180247553973542151 := by
  unfold tailWord_128310
  simp only [CollatzResearch.WordTrace]
  refine ⟨292490635322641153029899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3119900110108172298985589 292490635322641153029899)
  ·
    refine ⟨438735952983961729544849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292490635322641153029899 438735952983961729544849)
    ·
      refine ⟨329051964737971297158637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 438735952983961729544849 329051964737971297158637)
      ·
        refine ⟨123394486776739236434489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329051964737971297158637 123394486776739236434489)
        ·
          refine ⟨92545865082554427325867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123394486776739236434489 92545865082554427325867)
          ·
            refine ⟨138818797623831640988801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92545865082554427325867 138818797623831640988801)
            ·
              refine ⟨104114098217873730741601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138818797623831640988801 104114098217873730741601)
              ·
                refine ⟨78085573663405298056201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104114098217873730741601 78085573663405298056201)
                ·
                  refine ⟨58564180247553973542151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78085573663405298056201 58564180247553973542151)
                  ·
                    rfl

theorem cell20_128310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_128310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128310 prefixEnd_128310 := by exact prefixLift 128310
  have htrace : WordTrace (prefixWord ++ tailWord_128310) baseStart_128310 baseEnd_128310 := by
    simpa [prefixWord, tailWord_128310, baseEnd_128310] using wordTrace_append hprefix tailTrace_128310
  have hstable : (prefixWord ++ tailWord_128310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128310).length < 2 ^ (prefixWord ++ tailWord_128310).sum := by decide
  have hdescent : baseEnd_128310 < baseStart_128310 := by decide
  rcases family_descends (prefixWord ++ tailWord_128310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128318 : List Nat := [4, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_128318 : Nat := 118140960795 + 128318 * 2 ^ 59
def prefixEnd_128318 : Nat := 4983230072969 + 3 ^ 40 * 128318 * 2
def baseEnd_128318 : Nat := 58567831665541501275451

theorem tailTrace_128318 : CollatzResearch.WordTrace tailWord_128318 prefixEnd_128318 58567831665541501275451 := by
  unfold tailWord_128318
  simp only [CollatzResearch.WordTrace]
  refine ⟨585017743641659476846201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3120094632755517209846405 585017743641659476846201)
  ·
    refine ⟨438763307731244607634651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 585017743641659476846201 438763307731244607634651)
    ·
      refine ⟨658144961596866911451977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438763307731244607634651 658144961596866911451977)
      ·
        refine ⟨493608721197650183588983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658144961596866911451977 493608721197650183588983)
        ·
          refine ⟨740413081796475275383475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493608721197650183588983 740413081796475275383475)
          ·
            refine ⟨1110619622694712913075213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740413081796475275383475 1110619622694712913075213)
            ·
              refine ⟨416482358510517342403205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1110619622694712913075213 416482358510517342403205)
              ·
                refine ⟨78090442220722001700601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416482358510517342403205 78090442220722001700601)
                ·
                  refine ⟨58567831665541501275451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78090442220722001700601 58567831665541501275451)
                  ·
                    rfl

theorem cell20_128318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_128318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128318 prefixEnd_128318 := by exact prefixLift 128318
  have htrace : WordTrace (prefixWord ++ tailWord_128318) baseStart_128318 baseEnd_128318 := by
    simpa [prefixWord, tailWord_128318, baseEnd_128318] using wordTrace_append hprefix tailTrace_128318
  have hstable : (prefixWord ++ tailWord_128318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128318).length < 2 ^ (prefixWord ++ tailWord_128318).sum := by decide
  have hdescent : baseEnd_128318 < baseStart_128318 := by decide
  rcases family_descends (prefixWord ++ tailWord_128318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128329 : List Nat := [1, 2, 1, 1, 2, 3, 5, 5]
def baseStart_128329 : Nat := 118140960795 + 128329 * 2 ^ 59
def prefixEnd_128329 : Nat := 4983230072969 + 3 ^ 40 * 128329 * 2
def baseEnd_128329 : Nat := 19524284121758117302913

theorem tailTrace_128329 : CollatzResearch.WordTrace tailWord_128329 prefixEnd_128329 19524284121758117302913 := by
  unfold tailWord_128329
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680543152093424693420041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3120362101395616462280027 4680543152093424693420041)
  ·
    refine ⟨3510407364070068520065031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4680543152093424693420041 3510407364070068520065031)
    ·
      refine ⟨5265611046105102780097547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510407364070068520065031 5265611046105102780097547)
      ·
        refine ⟨7898416569157654170146321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5265611046105102780097547 7898416569157654170146321)
        ·
          refine ⟨5923812426868240627609741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7898416569157654170146321 5923812426868240627609741)
          ·
            refine ⟨2221429660075590235353653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5923812426868240627609741 2221429660075590235353653)
            ·
              refine ⟨208259030632086584564405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2221429660075590235353653 208259030632086584564405)
              ·
                refine ⟨19524284121758117302913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208259030632086584564405 19524284121758117302913)
                ·
                  rfl

theorem cell20_128329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_128329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128329 prefixEnd_128329 := by exact prefixLift 128329
  have htrace : WordTrace (prefixWord ++ tailWord_128329) baseStart_128329 baseEnd_128329 := by
    simpa [prefixWord, tailWord_128329, baseEnd_128329] using wordTrace_append hprefix tailTrace_128329
  have hstable : (prefixWord ++ tailWord_128329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128329).length < 2 ^ (prefixWord ++ tailWord_128329).sum := by decide
  have hdescent : baseEnd_128329 < baseStart_128329 := by decide
  rcases family_descends (prefixWord ++ tailWord_128329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128356 : List Nat := [2, 3, 1, 1, 3, 3, 2, 3, 2]
def baseStart_128356 : Nat := 118140960795 + 128356 * 2 ^ 59
def prefixEnd_128356 : Nat := 4983230072969 + 3 ^ 40 * 128356 * 2
def baseEnd_128356 : Nat := 58585175900982258008629

theorem tailTrace_128356 : CollatzResearch.WordTrace tailWord_128356 prefixEnd_128356 58585175900982258008629 := by
  unfold tailWord_128356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340763961497804152326461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3121018615330405536435281 2340763961497804152326461)
  ·
    refine ⟨877786485561676557122423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2340763961497804152326461 877786485561676557122423)
    ·
      refine ⟨1316679728342514835683635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877786485561676557122423 1316679728342514835683635)
      ·
        refine ⟨1975019592513772253525453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316679728342514835683635 1975019592513772253525453)
        ·
          refine ⟨740632347192664595072045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1975019592513772253525453 740632347192664595072045)
          ·
            refine ⟨277737130197249223152017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 740632347192664595072045 277737130197249223152017)
            ·
              refine ⟨208302847647936917364013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277737130197249223152017 208302847647936917364013)
              ·
                refine ⟨78113567867976344011505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208302847647936917364013 78113567867976344011505)
                ·
                  refine ⟨58585175900982258008629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78113567867976344011505 58585175900982258008629)
                  ·
                    rfl

theorem cell20_128356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_128356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128356 prefixEnd_128356 := by exact prefixLift 128356
  have htrace : WordTrace (prefixWord ++ tailWord_128356) baseStart_128356 baseEnd_128356 := by
    simpa [prefixWord, tailWord_128356, baseEnd_128356] using wordTrace_append hprefix tailTrace_128356
  have hstable : (prefixWord ++ tailWord_128356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128356).length < 2 ^ (prefixWord ++ tailWord_128356).sum := by decide
  have hdescent : baseEnd_128356 < baseStart_128356 := by decide
  rcases family_descends (prefixWord ++ tailWord_128356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128366 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_128366 : Nat := 118140960795 + 128366 * 2 ^ 59
def prefixEnd_128366 : Nat := 4983230072969 + 3 ^ 40 * 128366 * 2
def baseEnd_128366 : Nat := 58589740173466667675255

theorem tailTrace_128366 : CollatzResearch.WordTrace tailWord_128366 prefixEnd_128366 58589740173466667675255 := by
  unfold tailWord_128366
  simp only [CollatzResearch.WordTrace]
  refine ⟨585236581619922501564619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3121261768639586675011301 585236581619922501564619)
  ·
    refine ⟨877854872429883752346929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585236581619922501564619 877854872429883752346929)
    ·
      refine ⟨658391154322412814260197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 877854872429883752346929 658391154322412814260197)
      ·
        refine ⟨123448341435452402673787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 658391154322412814260197 123448341435452402673787)
        ·
          refine ⟨185172512153178604010681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123448341435452402673787 185172512153178604010681)
          ·
            refine ⟨138879384114883953008011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185172512153178604010681 138879384114883953008011)
            ·
              refine ⟨208319076172325929512017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138879384114883953008011 208319076172325929512017)
              ·
                refine ⟨156239307129244447134013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208319076172325929512017 156239307129244447134013)
                ·
                  refine ⟨58589740173466667675255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156239307129244447134013 58589740173466667675255)
                  ·
                    rfl

theorem cell20_128366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_128366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128366 prefixEnd_128366 := by exact prefixLift 128366
  have htrace : WordTrace (prefixWord ++ tailWord_128366) baseStart_128366 baseEnd_128366 := by
    simpa [prefixWord, tailWord_128366, baseEnd_128366] using wordTrace_append hprefix tailTrace_128366
  have hstable : (prefixWord ++ tailWord_128366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128366).length < 2 ^ (prefixWord ++ tailWord_128366).sum := by decide
  have hdescent : baseEnd_128366 < baseStart_128366 := by decide
  rcases family_descends (prefixWord ++ tailWord_128366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128377 : List Nat := [1, 2, 1, 3, 2, 1, 4, 4, 2]
def baseStart_128377 : Nat := 118140960795 + 128377 * 2 ^ 59
def prefixEnd_128377 : Nat := 4983230072969 + 3 ^ 40 * 128377 * 2
def baseEnd_128377 : Nat := 58594760873199518308543

theorem tailTrace_128377 : CollatzResearch.WordTrace tailWord_128377 prefixEnd_128377 58594760873199518308543 := by
  unfold tailWord_128377
  simp only [CollatzResearch.WordTrace]
  refine ⟨4682293855919528891167385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3121529237279685927444923 4682293855919528891167385)
  ·
    refine ⟨3511720391939646668375539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4682293855919528891167385 3511720391939646668375539)
    ·
      refine ⟨5267580587909470002563309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511720391939646668375539 5267580587909470002563309)
      ·
        refine ⟨1975342720466051250961241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5267580587909470002563309 1975342720466051250961241)
        ·
          refine ⟨1481507040349538438220931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1975342720466051250961241 1481507040349538438220931)
          ·
            refine ⟨2222260560524307657331397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481507040349538438220931 2222260560524307657331397)
            ·
              refine ⟨416673855098307685749637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2222260560524307657331397 416673855098307685749637)
              ·
                refine ⟨78126347830932691078057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416673855098307685749637 78126347830932691078057)
                ·
                  refine ⟨58594760873199518308543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78126347830932691078057 58594760873199518308543)
                  ·
                    rfl

theorem cell20_128377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_128377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128377 prefixEnd_128377 := by exact prefixLift 128377
  have htrace : WordTrace (prefixWord ++ tailWord_128377) baseStart_128377 baseEnd_128377 := by
    simpa [prefixWord, tailWord_128377, baseEnd_128377] using wordTrace_append hprefix tailTrace_128377
  have hstable : (prefixWord ++ tailWord_128377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128377).length < 2 ^ (prefixWord ++ tailWord_128377).sum := by decide
  have hdescent : baseEnd_128377 < baseStart_128377 := by decide
  rcases family_descends (prefixWord ++ tailWord_128377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128457 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_128457 : Nat := 118140960795 + 128457 * 2 ^ 59
def prefixEnd_128457 : Nat := 4983230072969 + 3 ^ 40 * 128457 * 2
def baseEnd_128457 : Nat := 58631275053074795641549

theorem tailTrace_128457 : CollatzResearch.WordTrace tailWord_128457 prefixEnd_128457 58631275053074795641549 := by
  unfold tailWord_128457
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685211695629702554079625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3123474463753135036053083 4685211695629702554079625)
  ·
    refine ⟨3513908771722276915559719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4685211695629702554079625 3513908771722276915559719)
    ·
      refine ⟨5270863157583415373339579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3513908771722276915559719 5270863157583415373339579)
      ·
        refine ⟨7906294736375123060009369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270863157583415373339579 7906294736375123060009369)
        ·
          refine ⟨5929721052281342295007027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7906294736375123060009369 5929721052281342295007027)
          ·
            refine ⟨8894581578422013442510541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929721052281342295007027 8894581578422013442510541)
            ·
              refine ⟨3335468091908255040941453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8894581578422013442510541 3335468091908255040941453)
              ·
                refine ⟨1250800534465595640353045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3335468091908255040941453 1250800534465595640353045)
                ·
                  refine ⟨58631275053074795641549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1250800534465595640353045 58631275053074795641549)
                  ·
                    rfl

theorem cell20_128457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_128457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128457 prefixEnd_128457 := by exact prefixLift 128457
  have htrace : WordTrace (prefixWord ++ tailWord_128457) baseStart_128457 baseEnd_128457 := by
    simpa [prefixWord, tailWord_128457, baseEnd_128457] using wordTrace_append hprefix tailTrace_128457
  have hstable : (prefixWord ++ tailWord_128457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128457).length < 2 ^ (prefixWord ++ tailWord_128457).sum := by decide
  have hdescent : baseEnd_128457 < baseStart_128457 := by decide
  rcases family_descends (prefixWord ++ tailWord_128457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128487 : List Nat := [1, 1, 5, 2, 1, 4, 2, 2, 2]
def baseStart_128487 : Nat := 118140960795 + 128487 * 2 ^ 59
def prefixEnd_128487 : Nat := 4983230072969 + 3 ^ 40 * 128487 * 2
def baseEnd_128487 : Nat := 58644967870528024641427

theorem tailTrace_128487 : CollatzResearch.WordTrace tailWord_128487 prefixEnd_128487 58644967870528024641427 := by
  unfold tailWord_128487
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686305885521017677671715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3124203923680678451781143 4686305885521017677671715)
  ·
    refine ⟨7029458828281526516507573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4686305885521017677671715 7029458828281526516507573)
    ·
      refine ⟨659011765151393110922585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7029458828281526516507573 659011765151393110922585)
      ·
        refine ⟨494258823863544833191939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659011765151393110922585 494258823863544833191939)
        ·
          refine ⟨741388235795317249787909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494258823863544833191939 741388235795317249787909)
          ·
            refine ⟨139010294211621984335233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 741388235795317249787909 139010294211621984335233)
            ·
              refine ⟨104257720658716488251425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139010294211621984335233 104257720658716488251425)
              ·
                refine ⟨78193290494037366188569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104257720658716488251425 78193290494037366188569)
                ·
                  refine ⟨58644967870528024641427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78193290494037366188569 58644967870528024641427)
                  ·
                    rfl

theorem cell20_128487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 2].length) (baseStart_128487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128487 prefixEnd_128487 := by exact prefixLift 128487
  have htrace : WordTrace (prefixWord ++ tailWord_128487) baseStart_128487 baseEnd_128487 := by
    simpa [prefixWord, tailWord_128487, baseEnd_128487] using wordTrace_append hprefix tailTrace_128487
  have hstable : (prefixWord ++ tailWord_128487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128487).length < 2 ^ (prefixWord ++ tailWord_128487).sum := by decide
  have hdescent : baseEnd_128487 < baseStart_128487 := by decide
  rcases family_descends (prefixWord ++ tailWord_128487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128498 : List Nat := [3, 2, 1, 4, 1, 1, 3, 5]
def baseStart_128498 : Nat := 118140960795 + 128498 * 2 ^ 59
def prefixEnd_128498 : Nat := 4983230072969 + 3 ^ 40 * 128498 * 2
def baseEnd_128498 : Nat := 19549996190086958424905

theorem tailTrace_128498 : CollatzResearch.WordTrace tailWord_128498 prefixEnd_128498 19549996190086958424905 := by
  unfold tailWord_128498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171676772120291639080537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3124471392320777704214765 1171676772120291639080537)
  ·
    refine ⟨878757579090218729310403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1171676772120291639080537 878757579090218729310403)
    ·
      refine ⟨1318136368635328093965605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878757579090218729310403 1318136368635328093965605)
      ·
        refine ⟨247150569119124017618551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1318136368635328093965605 247150569119124017618551)
        ·
          refine ⟨370725853678686026427827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247150569119124017618551 370725853678686026427827)
          ·
            refine ⟨556088780518029039641741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370725853678686026427827 556088780518029039641741)
            ·
              refine ⟨208533292694260889865653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556088780518029039641741 208533292694260889865653)
              ·
                refine ⟨19549996190086958424905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208533292694260889865653 19549996190086958424905)
                ·
                  rfl

theorem cell20_128498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_128498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128498 prefixEnd_128498 := by exact prefixLift 128498
  have htrace : WordTrace (prefixWord ++ tailWord_128498) baseStart_128498 baseEnd_128498 := by
    simpa [prefixWord, tailWord_128498, baseEnd_128498] using wordTrace_append hprefix tailTrace_128498
  have hstable : (prefixWord ++ tailWord_128498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128498).length < 2 ^ (prefixWord ++ tailWord_128498).sum := by decide
  have hdescent : baseEnd_128498 < baseStart_128498 := by decide
  rcases family_descends (prefixWord ++ tailWord_128498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128529 : List Nat := [1, 2, 2, 1, 1, 2, 6, 3, 2]
def baseStart_128529 : Nat := 118140960795 + 128529 * 2 ^ 59
def prefixEnd_128529 : Nat := 4983230072969 + 3 ^ 40 * 128529 * 2
def baseEnd_128529 : Nat := 58664137814962545241255

theorem tailTrace_128529 : CollatzResearch.WordTrace tailWord_128529 prefixEnd_128529 58664137814962545241255 := by
  unfold tailWord_128529
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687837751368858850700641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3125225167579239233800427 4687837751368858850700641)
  ·
    refine ⟨3515878313526644138025481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4687837751368858850700641 3515878313526644138025481)
    ·
      refine ⟨2636908735144983103519111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3515878313526644138025481 2636908735144983103519111)
      ·
        refine ⟨3955363102717474655278667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636908735144983103519111 3955363102717474655278667)
        ·
          refine ⟨5933044654076211982918001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955363102717474655278667 5933044654076211982918001)
          ·
            refine ⟨4449783490557158987188501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5933044654076211982918001 4449783490557158987188501)
            ·
              refine ⟨208583601119866827524461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4449783490557158987188501 208583601119866827524461)
              ·
                refine ⟨78218850419950060321673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208583601119866827524461 78218850419950060321673)
                ·
                  refine ⟨58664137814962545241255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78218850419950060321673 58664137814962545241255)
                  ·
                    rfl

theorem cell20_128529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_128529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128529 prefixEnd_128529 := by exact prefixLift 128529
  have htrace : WordTrace (prefixWord ++ tailWord_128529) baseStart_128529 baseEnd_128529 := by
    simpa [prefixWord, tailWord_128529, baseEnd_128529] using wordTrace_append hprefix tailTrace_128529
  have hstable : (prefixWord ++ tailWord_128529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128529).length < 2 ^ (prefixWord ++ tailWord_128529).sum := by decide
  have hdescent : baseEnd_128529 < baseStart_128529 := by decide
  rcases family_descends (prefixWord ++ tailWord_128529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128542 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_128542 : Nat := 118140960795 + 128542 * 2 ^ 59
def prefixEnd_128542 : Nat := 4983230072969 + 3 ^ 40 * 128542 * 2
def baseEnd_128542 : Nat := 58670071369192277807869

theorem tailTrace_128542 : CollatzResearch.WordTrace tailWord_128542 prefixEnd_128542 58670071369192277807869 := by
  unfold tailWord_128542
  simp only [CollatzResearch.WordTrace]
  refine ⟨586038987540220258865485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3125541266881174713949253 586038987540220258865485)
  ·
    refine ⟨219764620327582597074557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 586038987540220258865485 219764620327582597074557)
    ·
      refine ⟨82411732622843473902959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219764620327582597074557 82411732622843473902959)
      ·
        refine ⟨123617598934265210854439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82411732622843473902959 123617598934265210854439)
        ·
          refine ⟨185426398401397816281659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123617598934265210854439 185426398401397816281659)
          ·
            refine ⟨278139597602096724422489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185426398401397816281659 278139597602096724422489)
            ·
              refine ⟨208604698201572543316867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278139597602096724422489 208604698201572543316867)
              ·
                refine ⟨312907047302358814975301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208604698201572543316867 312907047302358814975301)
                ·
                  refine ⟨58670071369192277807869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 312907047302358814975301 58670071369192277807869)
                  ·
                    rfl

theorem cell20_128542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_128542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128542 prefixEnd_128542 := by exact prefixLift 128542
  have htrace : WordTrace (prefixWord ++ tailWord_128542) baseStart_128542 baseEnd_128542 := by
    simpa [prefixWord, tailWord_128542, baseEnd_128542] using wordTrace_append hprefix tailTrace_128542
  have hstable : (prefixWord ++ tailWord_128542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128542).length < 2 ^ (prefixWord ++ tailWord_128542).sum := by decide
  have hdescent : baseEnd_128542 < baseStart_128542 := by decide
  rcases family_descends (prefixWord ++ tailWord_128542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128543 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 3]
def baseStart_128543 : Nat := 118140960795 + 128543 * 2 ^ 59
def prefixEnd_128543 : Nat := 4983230072969 + 3 ^ 40 * 128543 * 2
def baseEnd_128543 : Nat := 58670527796440718774531

theorem tailTrace_128543 : CollatzResearch.WordTrace tailWord_128543 prefixEnd_128543 58670527796440718774531 := by
  unfold tailWord_128543
  simp only [CollatzResearch.WordTrace]
  refine ⟨4688348373318139241710283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3125565582212092827806855 4688348373318139241710283)
  ·
    refine ⟨7032522559977208862565425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4688348373318139241710283 7032522559977208862565425)
    ·
      refine ⟨5274391919982906646924069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7032522559977208862565425 5274391919982906646924069)
      ·
        refine ⟨988948484996794996298263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5274391919982906646924069 988948484996794996298263)
        ·
          refine ⟨1483422727495192494447395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988948484996794996298263 1483422727495192494447395)
          ·
            refine ⟨2225134091242788741671093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483422727495192494447395 2225134091242788741671093)
            ·
              refine ⟨208606321054011444531665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2225134091242788741671093 208606321054011444531665)
              ·
                refine ⟨156454740790508583398749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208606321054011444531665 156454740790508583398749)
                ·
                  refine ⟨58670527796440718774531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156454740790508583398749 58670527796440718774531)
                  ·
                    rfl

theorem cell20_128543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_128543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128543 prefixEnd_128543 := by exact prefixLift 128543
  have htrace : WordTrace (prefixWord ++ tailWord_128543) baseStart_128543 baseEnd_128543 := by
    simpa [prefixWord, tailWord_128543, baseEnd_128543] using wordTrace_append hprefix tailTrace_128543
  have hstable : (prefixWord ++ tailWord_128543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128543).length < 2 ^ (prefixWord ++ tailWord_128543).sum := by decide
  have hdescent : baseEnd_128543 < baseStart_128543 := by decide
  rcases family_descends (prefixWord ++ tailWord_128543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128747 : List Nat := [1, 1, 1, 1, 2, 4, 6, 4]
def baseStart_128747 : Nat := 118140960795 + 128747 * 2 ^ 59
def prefixEnd_128747 : Nat := 4983230072969 + 3 ^ 40 * 128747 * 2
def baseEnd_128747 : Nat := 19587879651707558657899

theorem tailTrace_128747 : CollatzResearch.WordTrace tailWord_128747 prefixEnd_128747 19587879651707558657899 := by
  unfold tailWord_128747
  simp only [CollatzResearch.WordTrace]
  refine ⟨4695788864579082082136495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3130525909719388054757663 4695788864579082082136495)
  ·
    refine ⟨7043683296868623123204743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4695788864579082082136495 7043683296868623123204743)
    ·
      refine ⟨10565524945302934684807115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7043683296868623123204743 10565524945302934684807115)
      ·
        refine ⟨15848287417954402027210673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10565524945302934684807115 15848287417954402027210673)
        ·
          refine ⟨11886215563465801520408005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15848287417954402027210673 11886215563465801520408005)
          ·
            refine ⟨2228665418149837785076501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11886215563465801520408005 2228665418149837785076501)
            ·
              refine ⟨104468691475773646175461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2228665418149837785076501 104468691475773646175461)
              ·
                refine ⟨19587879651707558657899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104468691475773646175461 19587879651707558657899)
                ·
                  rfl

theorem cell20_128747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 4].length) (baseStart_128747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128747 prefixEnd_128747 := by exact prefixLift 128747
  have htrace : WordTrace (prefixWord ++ tailWord_128747) baseStart_128747 baseEnd_128747 := by
    simpa [prefixWord, tailWord_128747, baseEnd_128747] using wordTrace_append hprefix tailTrace_128747
  have hstable : (prefixWord ++ tailWord_128747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128747).length < 2 ^ (prefixWord ++ tailWord_128747).sum := by decide
  have hdescent : baseEnd_128747 < baseStart_128747 := by decide
  rcases family_descends (prefixWord ++ tailWord_128747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128754 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_128754 : Nat := 118140960795 + 128754 * 2 ^ 59
def prefixEnd_128754 : Nat := 4983230072969 + 3 ^ 40 * 128754 * 2
def baseEnd_128754 : Nat := 58766833945861762740335

theorem tailTrace_128754 : CollatzResearch.WordTrace tailWord_128754 prefixEnd_128754 58766833945861762740335 := by
  unfold tailWord_128754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1174011043888430569410329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3130696117035814851760877 1174011043888430569410329)
  ·
    refine ⟨880508282916322927057747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1174011043888430569410329 880508282916322927057747)
    ·
      refine ⟨1320762424374484390586621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880508282916322927057747 1320762424374484390586621)
      ·
        refine ⟨495285909140431646469983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1320762424374484390586621 495285909140431646469983)
        ·
          refine ⟨742928863710647469704975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495285909140431646469983 742928863710647469704975)
          ·
            refine ⟨1114393295565971204557463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742928863710647469704975 1114393295565971204557463)
            ·
              refine ⟨1671589943348956806836195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114393295565971204557463 1671589943348956806836195)
              ·
                refine ⟨2507384915023435210254293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671589943348956806836195 2507384915023435210254293)
                ·
                  refine ⟨58766833945861762740335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2507384915023435210254293 58766833945861762740335)
                  ·
                    rfl

theorem cell20_128754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_128754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128754 prefixEnd_128754 := by exact prefixLift 128754
  have htrace : WordTrace (prefixWord ++ tailWord_128754) baseStart_128754 baseEnd_128754 := by
    simpa [prefixWord, tailWord_128754, baseEnd_128754] using wordTrace_append hprefix tailTrace_128754
  have hstable : (prefixWord ++ tailWord_128754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128754).length < 2 ^ (prefixWord ++ tailWord_128754).sum := by decide
  have hdescent : baseEnd_128754 < baseStart_128754 := by decide
  rcases family_descends (prefixWord ++ tailWord_128754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128778 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_128778 : Nat := 118140960795 + 128778 * 2 ^ 59
def prefixEnd_128778 : Nat := 4983230072969 + 3 ^ 40 * 128778 * 2
def baseEnd_128778 : Nat := 58777788199824345940237

theorem tailTrace_128778 : CollatzResearch.WordTrace tailWord_128778 prefixEnd_128778 58777788199824345940237 := by
  unfold tailWord_128778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1174229881866693594128747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3131279684977849584343325 1174229881866693594128747)
  ·
    refine ⟨1761344822800040391193121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1174229881866693594128747 1761344822800040391193121)
    ·
      refine ⟨1321008617100030293394841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1761344822800040391193121 1321008617100030293394841)
      ·
        refine ⟨990756462825022720046131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1321008617100030293394841 990756462825022720046131)
        ·
          refine ⟨1486134694237534080069197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990756462825022720046131 1486134694237534080069197)
          ·
            refine ⟨557300510339075280025949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1486134694237534080069197 557300510339075280025949)
            ·
              refine ⟨208987691377153230009731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557300510339075280025949 208987691377153230009731)
              ·
                refine ⟨313481537065729845014597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208987691377153230009731 313481537065729845014597)
                ·
                  refine ⟨58777788199824345940237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313481537065729845014597 58777788199824345940237)
                  ·
                    rfl

theorem cell20_128778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_128778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128778 prefixEnd_128778 := by exact prefixLift 128778
  have htrace : WordTrace (prefixWord ++ tailWord_128778) baseStart_128778 baseEnd_128778 := by
    simpa [prefixWord, tailWord_128778, baseEnd_128778] using wordTrace_append hprefix tailTrace_128778
  have hstable : (prefixWord ++ tailWord_128778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128778).length < 2 ^ (prefixWord ++ tailWord_128778).sum := by decide
  have hdescent : baseEnd_128778 < baseStart_128778 := by decide
  rcases family_descends (prefixWord ++ tailWord_128778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128799 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_128799 : Nat := 118140960795 + 128799 * 2 ^ 59
def prefixEnd_128799 : Nat := 4983230072969 + 3 ^ 40 * 128799 * 2
def baseEnd_128799 : Nat := 58787373172041606240151

theorem tailTrace_128799 : CollatzResearch.WordTrace tailWord_128799 prefixEnd_128799 58787373172041606240151 := by
  unfold tailWord_128799
  simp only [CollatzResearch.WordTrace]
  refine ⟨4697685460390694963029451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3131790306927129975352967 4697685460390694963029451)
  ·
    refine ⟨7046528190586042444544177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4697685460390694963029451 7046528190586042444544177)
    ·
      refine ⟨5284896142939531833408133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7046528190586042444544177 5284896142939531833408133)
      ·
        refine ⟨990918026801162218764025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5284896142939531833408133 990918026801162218764025)
        ·
          refine ⟨743188520100871664073019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990918026801162218764025 743188520100871664073019)
          ·
            refine ⟨1114782780151307496109529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743188520100871664073019 1114782780151307496109529)
            ·
              refine ⟨836087085113480622082147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114782780151307496109529 836087085113480622082147)
              ·
                refine ⟨1254130627670220933123221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836087085113480622082147 1254130627670220933123221)
                ·
                  refine ⟨58787373172041606240151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1254130627670220933123221 58787373172041606240151)
                  ·
                    rfl

theorem cell20_128799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_128799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128799 prefixEnd_128799 := by exact prefixLift 128799
  have htrace : WordTrace (prefixWord ++ tailWord_128799) baseStart_128799 baseEnd_128799 := by
    simpa [prefixWord, tailWord_128799, baseEnd_128799] using wordTrace_append hprefix tailTrace_128799
  have hstable : (prefixWord ++ tailWord_128799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128799).length < 2 ^ (prefixWord ++ tailWord_128799).sum := by decide
  have hdescent : baseEnd_128799 < baseStart_128799 := by decide
  rcases family_descends (prefixWord ++ tailWord_128799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128829 : List Nat := [1, 4, 1, 4, 1, 3, 2, 2, 2]
def baseStart_128829 : Nat := 118140960795 + 128829 * 2 ^ 59
def prefixEnd_128829 : Nat := 4983230072969 + 3 ^ 40 * 128829 * 2
def baseEnd_128829 : Nat := 58801065989494835240029

theorem tailTrace_128829 : CollatzResearch.WordTrace tailWord_128829 prefixEnd_128829 58801065989494835240029 := by
  unfold tailWord_128829
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698779650282010086621541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3132519766854673391081027 4698779650282010086621541)
  ·
    refine ⟨881021184427876891241539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4698779650282010086621541 881021184427876891241539)
    ·
      refine ⟨1321531776641815336862309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 881021184427876891241539 1321531776641815336862309)
      ·
        refine ⟨247787208120340375661683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1321531776641815336862309 247787208120340375661683)
        ·
          refine ⟨371680812180510563492525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247787208120340375661683 371680812180510563492525)
          ·
            refine ⟨139380304567691461309697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371680812180510563492525 139380304567691461309697)
            ·
              refine ⟨104535228425768595982273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139380304567691461309697 104535228425768595982273)
              ·
                refine ⟨78401421319326446986705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104535228425768595982273 78401421319326446986705)
                ·
                  refine ⟨58801065989494835240029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78401421319326446986705 58801065989494835240029)
                  ·
                    rfl

theorem cell20_128829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_128829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128829 prefixEnd_128829 := by exact prefixLift 128829
  have htrace : WordTrace (prefixWord ++ tailWord_128829) baseStart_128829 baseEnd_128829 := by
    simpa [prefixWord, tailWord_128829, baseEnd_128829] using wordTrace_append hprefix tailTrace_128829
  have hstable : (prefixWord ++ tailWord_128829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128829).length < 2 ^ (prefixWord ++ tailWord_128829).sum := by decide
  have hdescent : baseEnd_128829 < baseStart_128829 := by decide
  rcases family_descends (prefixWord ++ tailWord_128829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128837 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_128837 : Nat := 118140960795 + 128837 * 2 ^ 59
def prefixEnd_128837 : Nat := 4983230072969 + 3 ^ 40 * 128837 * 2
def baseEnd_128837 : Nat := 58804717407482362973329

theorem tailTrace_128837 : CollatzResearch.WordTrace tailWord_128837 prefixEnd_128837 58804717407482362973329 := by
  unfold tailWord_128837
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699071434253027452912765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3132714289502018301941843 4699071434253027452912765)
  ·
    refine ⟨1762151787844885294842287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4699071434253027452912765 1762151787844885294842287)
    ·
      refine ⟨2643227681767327942263431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762151787844885294842287 2643227681767327942263431)
      ·
        refine ⟨3964841522650991913395147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643227681767327942263431 3964841522650991913395147)
        ·
          refine ⟨5947262283976487870092721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964841522650991913395147 5947262283976487870092721)
          ·
            refine ⟨4460446712982365902569541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5947262283976487870092721 4460446712982365902569541)
            ·
              refine ⟨836333758684193606731789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4460446712982365902569541 836333758684193606731789)
              ·
                refine ⟨313625159506572602524421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 836333758684193606731789 313625159506572602524421)
                ·
                  refine ⟨58804717407482362973329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313625159506572602524421 58804717407482362973329)
                  ·
                    rfl

theorem cell20_128837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_128837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128837 prefixEnd_128837 := by exact prefixLift 128837
  have htrace : WordTrace (prefixWord ++ tailWord_128837) baseStart_128837 baseEnd_128837 := by
    simpa [prefixWord, tailWord_128837, baseEnd_128837] using wordTrace_append hprefix tailTrace_128837
  have hstable : (prefixWord ++ tailWord_128837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128837).length < 2 ^ (prefixWord ++ tailWord_128837).sum := by decide
  have hdescent : baseEnd_128837 < baseStart_128837 := by decide
  rcases family_descends (prefixWord ++ tailWord_128837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128851 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_128851 : Nat := 118140960795 + 128851 * 2 ^ 59
def prefixEnd_128851 : Nat := 4983230072969 + 3 ^ 40 * 128851 * 2
def baseEnd_128851 : Nat := 58811107388960536506605

theorem tailTrace_128851 : CollatzResearch.WordTrace tailWord_128851 prefixEnd_128851 58811107388960536506605 := by
  unfold tailWord_128851
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699582056202307843922407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3133054704134871895948271 4699582056202307843922407)
  ·
    refine ⟨7049373084303461765883611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4699582056202307843922407 7049373084303461765883611)
    ·
      refine ⟨10574059626455192648825417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7049373084303461765883611 10574059626455192648825417)
      ·
        refine ⟨7930544719841394486619063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10574059626455192648825417 7930544719841394486619063)
        ·
          refine ⟨11895817079762091729928595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7930544719841394486619063 11895817079762091729928595)
          ·
            refine ⟨17843725619643137594892893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11895817079762091729928595 17843725619643137594892893)
            ·
              refine ⟨6691397107366176598084835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17843725619643137594892893 6691397107366176598084835)
              ·
                refine ⟨10037095661049264897127253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691397107366176598084835 10037095661049264897127253)
                ·
                  refine ⟨58811107388960536506605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10037095661049264897127253 58811107388960536506605)
                  ·
                    rfl

theorem cell20_128851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_128851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128851 prefixEnd_128851 := by exact prefixLift 128851
  have htrace : WordTrace (prefixWord ++ tailWord_128851) baseStart_128851 baseEnd_128851 := by
    simpa [prefixWord, tailWord_128851, baseEnd_128851] using wordTrace_append hprefix tailTrace_128851
  have hstable : (prefixWord ++ tailWord_128851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128851).length < 2 ^ (prefixWord ++ tailWord_128851).sum := by decide
  have hdescent : baseEnd_128851 < baseStart_128851 := by decide
  rcases family_descends (prefixWord ++ tailWord_128851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128871 : List Nat := [1, 1, 5, 1, 2, 1, 4, 3, 2]
def baseStart_128871 : Nat := 118140960795 + 128871 * 2 ^ 59
def prefixEnd_128871 : Nat := 4983230072969 + 3 ^ 40 * 128871 * 2
def baseEnd_128871 : Nat := 58820235933929355839857

theorem tailTrace_128871 : CollatzResearch.WordTrace tailWord_128871 prefixEnd_128871 58820235933929355839857 := by
  unfold tailWord_128871
  simp only [CollatzResearch.WordTrace]
  refine ⟨4700311516129851259650467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3133541010753234173100311 4700311516129851259650467)
  ·
    refine ⟨7050467274194776889475701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4700311516129851259650467 7050467274194776889475701)
    ·
      refine ⟨660981306955760333388347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7050467274194776889475701 660981306955760333388347)
      ·
        refine ⟨991471960433640500082521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660981306955760333388347 991471960433640500082521)
        ·
          refine ⟨743603970325230375061891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991471960433640500082521 743603970325230375061891)
          ·
            refine ⟨1115405955487845562592837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743603970325230375061891 1115405955487845562592837)
            ·
              refine ⟨209138616653971042986157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1115405955487845562592837 209138616653971042986157)
              ·
                refine ⟨78426981245239141119809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209138616653971042986157 78426981245239141119809)
                ·
                  refine ⟨58820235933929355839857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78426981245239141119809 58820235933929355839857)
                  ·
                    rfl

theorem cell20_128871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 2].length) (baseStart_128871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128871 prefixEnd_128871 := by exact prefixLift 128871
  have htrace : WordTrace (prefixWord ++ tailWord_128871) baseStart_128871 baseEnd_128871 := by
    simpa [prefixWord, tailWord_128871, baseEnd_128871] using wordTrace_append hprefix tailTrace_128871
  have hstable : (prefixWord ++ tailWord_128871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128871).length < 2 ^ (prefixWord ++ tailWord_128871).sum := by decide
  have hdescent : baseEnd_128871 < baseStart_128871 := by decide
  rcases family_descends (prefixWord ++ tailWord_128871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128913 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_128913 : Nat := 118140960795 + 128913 * 2 ^ 59
def prefixEnd_128913 : Nat := 4983230072969 + 3 ^ 40 * 128913 * 2
def baseEnd_128913 : Nat := 58839405878363876439685

theorem tailTrace_128913 : CollatzResearch.WordTrace tailWord_128913 prefixEnd_128913 58839405878363876439685 := by
  unfold tailWord_128913
  simp only [CollatzResearch.WordTrace]
  refine ⟨4701843381977692432679393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3134562254651794955119595 4701843381977692432679393)
  ·
    refine ⟨3526382536483269324509545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4701843381977692432679393 3526382536483269324509545)
    ·
      refine ⟨2644786902362451993382159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3526382536483269324509545 2644786902362451993382159)
      ·
        refine ⟨3967180353543677990073239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644786902362451993382159 3967180353543677990073239)
        ·
          refine ⟨5950770530315516985109859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967180353543677990073239 5950770530315516985109859)
          ·
            refine ⟨8926155795473275477664789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5950770530315516985109859 8926155795473275477664789)
            ·
              refine ⟨418413552912809788015537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8926155795473275477664789 418413552912809788015537)
              ·
                refine ⟨313810164684607341011653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418413552912809788015537 313810164684607341011653)
                ·
                  refine ⟨58839405878363876439685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313810164684607341011653 58839405878363876439685)
                  ·
                    rfl

theorem cell20_128913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_128913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128913 prefixEnd_128913 := by exact prefixLift 128913
  have htrace : WordTrace (prefixWord ++ tailWord_128913) baseStart_128913 baseEnd_128913 := by
    simpa [prefixWord, tailWord_128913, baseEnd_128913] using wordTrace_append hprefix tailTrace_128913
  have hstable : (prefixWord ++ tailWord_128913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128913).length < 2 ^ (prefixWord ++ tailWord_128913).sum := by decide
  have hdescent : baseEnd_128913 < baseStart_128913 := by decide
  rcases family_descends (prefixWord ++ tailWord_128913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128916 : List Nat := [2, 4, 2, 1, 1, 2, 4, 4]
def baseStart_128916 : Nat := 118140960795 + 128916 * 2 ^ 59
def prefixEnd_128916 : Nat := 4983230072969 + 3 ^ 40 * 128916 * 2
def baseEnd_128916 : Nat := 19613591720036399779891

theorem tailTrace_128916 : CollatzResearch.WordTrace tailWord_128916 prefixEnd_128916 19613591720036399779891 := by
  unfold tailWord_128916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2350976400483411972519301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3134635200644549296692401 2350976400483411972519301)
  ·
    refine ⟨440808075090639744847369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2350976400483411972519301 440808075090639744847369)
    ·
      refine ⟨330606056317979808635527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440808075090639744847369 330606056317979808635527)
      ·
        refine ⟨495909084476969712953291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330606056317979808635527 495909084476969712953291)
        ·
          refine ⟨743863626715454569429937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495909084476969712953291 743863626715454569429937)
          ·
            refine ⟨557897720036590927072453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743863626715454569429937 557897720036590927072453)
            ·
              refine ⟨104605822506860798826085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 557897720036590927072453 104605822506860798826085)
              ·
                refine ⟨19613591720036399779891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104605822506860798826085 19613591720036399779891)
                ·
                  rfl

theorem cell20_128916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_128916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128916 prefixEnd_128916 := by exact prefixLift 128916
  have htrace : WordTrace (prefixWord ++ tailWord_128916) baseStart_128916 baseEnd_128916 := by
    simpa [prefixWord, tailWord_128916, baseEnd_128916] using wordTrace_append hprefix tailTrace_128916
  have hstable : (prefixWord ++ tailWord_128916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128916).length < 2 ^ (prefixWord ++ tailWord_128916).sum := by decide
  have hdescent : baseEnd_128916 < baseStart_128916 := by decide
  rcases family_descends (prefixWord ++ tailWord_128916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128947 : List Nat := [1, 1, 1, 2, 3, 1, 7, 2, 2]
def baseStart_128947 : Nat := 118140960795 + 128947 * 2 ^ 59
def prefixEnd_128947 : Nat := 4983230072969 + 3 ^ 40 * 128947 * 2
def baseEnd_128947 : Nat := 58854924404810869306213

theorem tailTrace_128947 : CollatzResearch.WordTrace tailWord_128947 prefixEnd_128947 58854924404810869306213 := by
  unfold tailWord_128947
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703083463854516239417095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3135388975903010826278063 4703083463854516239417095)
  ·
    refine ⟨7054625195781774359125643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4703083463854516239417095 7054625195781774359125643)
    ·
      refine ⟨10581937793672661538688465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7054625195781774359125643 10581937793672661538688465)
      ·
        refine ⟨7936453345254496154016349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10581937793672661538688465 7936453345254496154016349)
        ·
          refine ⟨2976170004470436057756131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7936453345254496154016349 2976170004470436057756131)
          ·
            refine ⟨4464255006705654086634197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976170004470436057756131 4464255006705654086634197)
            ·
              refine ⟨104630976719663767655489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4464255006705654086634197 104630976719663767655489)
              ·
                refine ⟨78473232539747825741617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104630976719663767655489 78473232539747825741617)
                ·
                  refine ⟨58854924404810869306213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78473232539747825741617 58854924404810869306213)
                  ·
                    rfl

theorem cell20_128947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 2].length) (baseStart_128947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128947 prefixEnd_128947 := by exact prefixLift 128947
  have htrace : WordTrace (prefixWord ++ tailWord_128947) baseStart_128947 baseEnd_128947 := by
    simpa [prefixWord, tailWord_128947, baseEnd_128947] using wordTrace_append hprefix tailTrace_128947
  have hstable : (prefixWord ++ tailWord_128947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128947).length < 2 ^ (prefixWord ++ tailWord_128947).sum := by decide
  have hdescent : baseEnd_128947 < baseStart_128947 := by decide
  rcases family_descends (prefixWord ++ tailWord_128947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128965 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_128965 : Nat := 118140960795 + 128965 * 2 ^ 59
def prefixEnd_128965 : Nat := 4983230072969 + 3 ^ 40 * 128965 * 2
def baseEnd_128965 : Nat := 58863140095282806706139

theorem tailTrace_128965 : CollatzResearch.WordTrace tailWord_128965 prefixEnd_128965 58863140095282806706139 := by
  unfold tailWord_128965
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703739977789305313572349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3135826651859536875714899 4703739977789305313572349)
  ·
    refine ⟨1763902491670989492589631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4703739977789305313572349 1763902491670989492589631)
    ·
      refine ⟨2645853737506484238884447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763902491670989492589631 2645853737506484238884447)
      ·
        refine ⟨3968780606259726358326671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645853737506484238884447 3968780606259726358326671)
        ·
          refine ⟨5953170909389589537490007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968780606259726358326671 5953170909389589537490007)
          ·
            refine ⟨8929756364084384306235011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953170909389589537490007 8929756364084384306235011)
            ·
              refine ⟨13394634546126576459352517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8929756364084384306235011 13394634546126576459352517)
              ·
                refine ⟨2511493977398733086128597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13394634546126576459352517 2511493977398733086128597)
                ·
                  refine ⟨58863140095282806706139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2511493977398733086128597 58863140095282806706139)
                  ·
                    rfl

theorem cell20_128965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_128965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_128965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_128965 prefixEnd_128965 := by exact prefixLift 128965
  have htrace : WordTrace (prefixWord ++ tailWord_128965) baseStart_128965 baseEnd_128965 := by
    simpa [prefixWord, tailWord_128965, baseEnd_128965] using wordTrace_append hprefix tailTrace_128965
  have hstable : (prefixWord ++ tailWord_128965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128965).length < 2 ^ (prefixWord ++ tailWord_128965).sum := by decide
  have hdescent : baseEnd_128965 < baseStart_128965 := by decide
  rcases family_descends (prefixWord ++ tailWord_128965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129003 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_129003 : Nat := 118140960795 + 129003 * 2 ^ 59
def prefixEnd_129003 : Nat := 4983230072969 + 3 ^ 40 * 129003 * 2
def baseEnd_129003 : Nat := 58880484330723563439317

theorem tailTrace_129003 : CollatzResearch.WordTrace tailWord_129003 prefixEnd_129003 58880484330723563439317 := by
  unfold tailWord_129003
  simp only [CollatzResearch.WordTrace]
  refine ⟨4705125951651637803455663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3136750634434425202303775 4705125951651637803455663)
  ·
    refine ⟨7057688927477456705183495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4705125951651637803455663 7057688927477456705183495)
    ·
      refine ⟨10586533391216185057775243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7057688927477456705183495 10586533391216185057775243)
      ·
        refine ⟨15879800086824277586662865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10586533391216185057775243 15879800086824277586662865)
        ·
          refine ⟨11909850065118208189997149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15879800086824277586662865 11909850065118208189997149)
          ·
            refine ⟨4466193774419328071248931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11909850065118208189997149 4466193774419328071248931)
            ·
              refine ⟨6699290661628992106873397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466193774419328071248931 6699290661628992106873397)
              ·
                refine ⟨628058499527718010019381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6699290661628992106873397 628058499527718010019381)
                ·
                  refine ⟨58880484330723563439317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 628058499527718010019381 58880484330723563439317)
                  ·
                    rfl

theorem cell20_129003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_129003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129003 prefixEnd_129003 := by exact prefixLift 129003
  have htrace : WordTrace (prefixWord ++ tailWord_129003) baseStart_129003 baseEnd_129003 := by
    simpa [prefixWord, tailWord_129003, baseEnd_129003] using wordTrace_append hprefix tailTrace_129003
  have hstable : (prefixWord ++ tailWord_129003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129003).length < 2 ^ (prefixWord ++ tailWord_129003).sum := by decide
  have hdescent : baseEnd_129003 < baseStart_129003 := by decide
  rcases family_descends (prefixWord ++ tailWord_129003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129020 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_129020 : Nat := 118140960795 + 129020 * 2 ^ 59
def prefixEnd_129020 : Nat := 4983230072969 + 3 ^ 40 * 129020 * 2
def baseEnd_129020 : Nat := 58888243593947059872581

theorem tailTrace_129020 : CollatzResearch.WordTrace tailWord_129020 prefixEnd_129020 58888243593947059872581 := by
  unfold tailWord_129020
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352872996295024853412257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3137163995060033137883009 2352872996295024853412257)
  ·
    refine ⟨1764654747221268640059193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2352872996295024853412257 1764654747221268640059193)
    ·
      refine ⟨1323491060415951480044395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1764654747221268640059193 1323491060415951480044395)
      ·
        refine ⟨1985236590623927220066593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323491060415951480044395 1985236590623927220066593)
        ·
          refine ⟨1488927442967945415049945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1985236590623927220066593 1488927442967945415049945)
          ·
            refine ⟨1116695582225959061287459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1488927442967945415049945 1116695582225959061287459)
            ·
              refine ⟨1675043373338938591931189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116695582225959061287459 1675043373338938591931189)
              ·
                refine ⟨157035316250525492993549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1675043373338938591931189 157035316250525492993549)
                ·
                  refine ⟨58888243593947059872581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157035316250525492993549 58888243593947059872581)
                  ·
                    rfl

theorem cell20_129020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_129020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129020 prefixEnd_129020 := by exact prefixLift 129020
  have htrace : WordTrace (prefixWord ++ tailWord_129020) baseStart_129020 baseEnd_129020 := by
    simpa [prefixWord, tailWord_129020, baseEnd_129020] using wordTrace_append hprefix tailTrace_129020
  have hstable : (prefixWord ++ tailWord_129020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129020).length < 2 ^ (prefixWord ++ tailWord_129020).sum := by decide
  have hdescent : baseEnd_129020 < baseStart_129020 := by decide
  rcases family_descends (prefixWord ++ tailWord_129020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129058 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_129058 : Nat := 118140960795 + 129058 * 2 ^ 59
def prefixEnd_129058 : Nat := 4983230072969 + 3 ^ 40 * 129058 * 2
def baseEnd_129058 : Nat := 58905587829387816605759

theorem tailTrace_129058 : CollatzResearch.WordTrace tailWord_129058 prefixEnd_129058 58905587829387816605759 := by
  unfold tailWord_129058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176782991613095549176957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3138087977634921464471885 1176782991613095549176957)
  ·
    refine ⟨441293621854910830941359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1176782991613095549176957 441293621854910830941359)
    ·
      refine ⟨661940432782366246412039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441293621854910830941359 661940432782366246412039)
      ·
        refine ⟨992910649173549369618059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661940432782366246412039 992910649173549369618059)
        ·
          refine ⟨1489365973760324054427089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992910649173549369618059 1489365973760324054427089)
          ·
            refine ⟨1117024480320243040820317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1489365973760324054427089 1117024480320243040820317)
            ·
              refine ⟨418884180120091140307619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1117024480320243040820317 418884180120091140307619)
              ·
                refine ⟨628326270180136710461429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418884180120091140307619 628326270180136710461429)
                ·
                  refine ⟨58905587829387816605759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 628326270180136710461429 58905587829387816605759)
                  ·
                    rfl

theorem cell20_129058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_129058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129058 prefixEnd_129058 := by exact prefixLift 129058
  have htrace : WordTrace (prefixWord ++ tailWord_129058) baseStart_129058 baseEnd_129058 := by
    simpa [prefixWord, tailWord_129058, baseEnd_129058] using wordTrace_append hprefix tailTrace_129058
  have hstable : (prefixWord ++ tailWord_129058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129058).length < 2 ^ (prefixWord ++ tailWord_129058).sum := by decide
  have hdescent : baseEnd_129058 < baseStart_129058 := by decide
  rcases family_descends (prefixWord ++ tailWord_129058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129089 : List Nat := [1, 2, 5, 1, 2, 2, 1, 6]
def baseStart_129089 : Nat := 118140960795 + 129089 * 2 ^ 59
def prefixEnd_129089 : Nat := 4983230072969 + 3 ^ 40 * 129089 * 2
def baseEnd_129089 : Nat := 19639912358029828857433

theorem tailTrace_129089 : CollatzResearch.WordTrace tailWord_129089 prefixEnd_129089 19639912358029828857433 := by
  unfold tailWord_129089
  simp only [CollatzResearch.WordTrace]
  refine ⟨4708262629340074491086321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3138841752893382994057547 4708262629340074491086321)
  ·
    refine ⟨3531196972005055868314741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4708262629340074491086321 3531196972005055868314741)
    ·
      refine ⟨331049716125473987654507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3531196972005055868314741 331049716125473987654507)
      ·
        refine ⟨496574574188210981481761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331049716125473987654507 496574574188210981481761)
        ·
          refine ⟨372430930641158236111321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496574574188210981481761 372430930641158236111321)
          ·
            refine ⟨279323197980868677083491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372430930641158236111321 279323197980868677083491)
            ·
              refine ⟨418984796971303015625237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279323197980868677083491 418984796971303015625237)
              ·
                refine ⟨19639912358029828857433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 418984796971303015625237 19639912358029828857433)
                ·
                  rfl

theorem cell20_129089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_129089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129089 prefixEnd_129089 := by exact prefixLift 129089
  have htrace : WordTrace (prefixWord ++ tailWord_129089) baseStart_129089 baseEnd_129089 := by
    simpa [prefixWord, tailWord_129089, baseEnd_129089] using wordTrace_append hprefix tailTrace_129089
  have hstable : (prefixWord ++ tailWord_129089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129089).length < 2 ^ (prefixWord ++ tailWord_129089).sum := by decide
  have hdescent : baseEnd_129089 < baseStart_129089 := by decide
  rcases family_descends (prefixWord ++ tailWord_129089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129106 : List Nat := [3, 2, 2, 1, 5, 1, 6]
def baseStart_129106 : Nat := 118140960795 + 129106 * 2 ^ 59
def prefixEnd_129106 : Nat := 4983230072969 + 3 ^ 40 * 129106 * 2
def baseEnd_129106 : Nat := 6547499593034775889507

theorem tailTrace_129106 : CollatzResearch.WordTrace tailWord_129106 prefixEnd_129106 6547499593034775889507 := by
  unfold tailWord_129106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177220667569621598613793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3139255113518990929636781 1177220667569621598613793)
  ·
    refine ⟨882915500677216198960345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1177220667569621598613793 882915500677216198960345)
    ·
      refine ⟨662186625507912149220259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 882915500677216198960345 662186625507912149220259)
      ·
        refine ⟨993279938261868223830389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662186625507912149220259 993279938261868223830389)
        ·
          refine ⟨93119994212050145984099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 993279938261868223830389 93119994212050145984099)
          ·
            refine ⟨139679991318075218976149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93119994212050145984099 139679991318075218976149)
            ·
              refine ⟨6547499593034775889507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139679991318075218976149 6547499593034775889507)
              ·
                rfl

theorem cell20_129106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 6].length) (baseStart_129106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129106 prefixEnd_129106 := by exact prefixLift 129106
  have htrace : WordTrace (prefixWord ++ tailWord_129106) baseStart_129106 baseEnd_129106 := by
    simpa [prefixWord, tailWord_129106, baseEnd_129106] using wordTrace_append hprefix tailTrace_129106
  have hstable : (prefixWord ++ tailWord_129106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129106).length < 2 ^ (prefixWord ++ tailWord_129106).sum := by decide
  have hdescent : baseEnd_129106 < baseStart_129106 := by decide
  rcases family_descends (prefixWord ++ tailWord_129106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129116 : List Nat := [2, 2, 4, 1, 1, 3, 3, 2, 2]
def baseStart_129116 : Nat := 118140960795 + 129116 * 2 ^ 59
def prefixEnd_129116 : Nat := 4983230072969 + 3 ^ 40 * 129116 * 2
def baseEnd_129116 : Nat := 58932060609797392672189

theorem tailTrace_129116 : CollatzResearch.WordTrace tailWord_129116 prefixEnd_129116 58932060609797392672189 := by
  unfold tailWord_129116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2354623700121129051159601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3139498266828172068212801 2354623700121129051159601)
  ·
    refine ⟨1765967775090846788369701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2354623700121129051159601 1765967775090846788369701)
    ·
      refine ⟨331118957829533772819319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1765967775090846788369701 331118957829533772819319)
      ·
        refine ⟨496678436744300659228979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331118957829533772819319 496678436744300659228979)
        ·
          refine ⟨745017655116450988843469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496678436744300659228979 745017655116450988843469)
          ·
            refine ⟨279381620668669120816301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 745017655116450988843469 279381620668669120816301)
            ·
              refine ⟨104768107750750920306113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279381620668669120816301 104768107750750920306113)
              ·
                refine ⟨78576080813063190229585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104768107750750920306113 78576080813063190229585)
                ·
                  refine ⟨58932060609797392672189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78576080813063190229585 58932060609797392672189)
                  ·
                    rfl

theorem cell20_129116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_129116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129116 prefixEnd_129116 := by exact prefixLift 129116
  have htrace : WordTrace (prefixWord ++ tailWord_129116) baseStart_129116 baseEnd_129116 := by
    simpa [prefixWord, tailWord_129116, baseEnd_129116] using wordTrace_append hprefix tailTrace_129116
  have hstable : (prefixWord ++ tailWord_129116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129116).length < 2 ^ (prefixWord ++ tailWord_129116).sum := by decide
  have hdescent : baseEnd_129116 < baseStart_129116 := by decide
  rcases family_descends (prefixWord ++ tailWord_129116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129120 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 4]
def baseStart_129120 : Nat := 118140960795 + 129120 * 2 ^ 59
def prefixEnd_129120 : Nat := 4983230072969 + 3 ^ 40 * 129120 * 2
def baseEnd_129120 : Nat := 58933886318791156538839

theorem tailTrace_129120 : CollatzResearch.WordTrace tailWord_129120 prefixEnd_129120 58933886318791156538839 := by
  unfold tailWord_129120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2354696646113883392732407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3139595528151844523643209 2354696646113883392732407)
  ·
    refine ⟨3532044969170825089098611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2354696646113883392732407 3532044969170825089098611)
    ·
      refine ⟨5298067453756237633647917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3532044969170825089098611 5298067453756237633647917)
      ·
        refine ⟨1986775295158589112617969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5298067453756237633647917 1986775295158589112617969)
        ·
          refine ⟨1490081471368941834463477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1986775295158589112617969 1490081471368941834463477)
          ·
            refine ⟨139695137940838296980951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1490081471368941834463477 139695137940838296980951)
            ·
              refine ⟨209542706911257445471427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139695137940838296980951 209542706911257445471427)
              ·
                refine ⟨314314060366886168207141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209542706911257445471427 314314060366886168207141)
                ·
                  refine ⟨58933886318791156538839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314314060366886168207141 58933886318791156538839)
                  ·
                    rfl

theorem cell20_129120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_129120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129120 prefixEnd_129120 := by exact prefixLift 129120
  have htrace : WordTrace (prefixWord ++ tailWord_129120) baseStart_129120 baseEnd_129120 := by
    simpa [prefixWord, tailWord_129120, baseEnd_129120] using wordTrace_append hprefix tailTrace_129120
  have hstable : (prefixWord ++ tailWord_129120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129120).length < 2 ^ (prefixWord ++ tailWord_129120).sum := by decide
  have hdescent : baseEnd_129120 < baseStart_129120 := by decide
  rcases family_descends (prefixWord ++ tailWord_129120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129148 : List Nat := [2, 2, 2, 1, 1, 4, 2, 6]
def baseStart_129148 : Nat := 118140960795 + 129148 * 2 ^ 59
def prefixEnd_129148 : Nat := 4983230072969 + 3 ^ 40 * 129148 * 2
def baseEnd_129148 : Nat := 19648888760582501201797

theorem tailTrace_129148 : CollatzResearch.WordTrace tailWord_129148 prefixEnd_129148 19648888760582501201797 := by
  unfold tailWord_129148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2355207268063163783742049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3140276357417551711656065 2355207268063163783742049)
  ·
    refine ⟨1766405451047372837806537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2355207268063163783742049 1766405451047372837806537)
    ·
      refine ⟨1324804088285529628354903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1766405451047372837806537 1324804088285529628354903)
      ·
        refine ⟨1987206132428294442532355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324804088285529628354903 1987206132428294442532355)
        ·
          refine ⟨2980809198642441663798533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987206132428294442532355 2980809198642441663798533)
          ·
            refine ⟨558901724745457811962225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2980809198642441663798533 558901724745457811962225)
            ·
              refine ⟨419176293559093358971669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558901724745457811962225 419176293559093358971669)
              ·
                refine ⟨19648888760582501201797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 419176293559093358971669 19648888760582501201797)
                ·
                  rfl

theorem cell20_129148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_129148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129148 prefixEnd_129148 := by exact prefixLift 129148
  have htrace : WordTrace (prefixWord ++ tailWord_129148) baseStart_129148 baseEnd_129148 := by
    simpa [prefixWord, tailWord_129148, baseEnd_129148] using wordTrace_append hprefix tailTrace_129148
  have hstable : (prefixWord ++ tailWord_129148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129148).length < 2 ^ (prefixWord ++ tailWord_129148).sum := by decide
  have hdescent : baseEnd_129148 < baseStart_129148 := by decide
  rcases family_descends (prefixWord ++ tailWord_129148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129174 : List Nat := [5, 3, 2, 1, 2, 1, 1, 5]
def baseStart_129174 : Nat := 118140960795 + 129174 * 2 ^ 59
def prefixEnd_129174 : Nat := 4983230072969 + 3 ^ 40 * 129174 * 2
def baseEnd_129174 : Nat := 19652844463402322912873

theorem tailTrace_129174 : CollatzResearch.WordTrace tailWord_129174 prefixEnd_129174 19652844463402322912873 := by
  unfold tailWord_129174
  simp only [CollatzResearch.WordTrace]
  refine ⟨294460177127008375495661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3140908556021422671953717 294460177127008375495661)
  ·
    refine ⟨110422566422628140810873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294460177127008375495661 110422566422628140810873)
    ·
      refine ⟨82816924816971105608155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110422566422628140810873 82816924816971105608155)
      ·
        refine ⟨124225387225456658412233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82816924816971105608155 124225387225456658412233)
        ·
          refine ⟨93169040419092493809175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124225387225456658412233 93169040419092493809175)
          ·
            refine ⟨139753560628638740713763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93169040419092493809175 139753560628638740713763)
            ·
              refine ⟨209630340942958111070645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139753560628638740713763 209630340942958111070645)
              ·
                refine ⟨19652844463402322912873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209630340942958111070645 19652844463402322912873)
                ·
                  rfl

theorem cell20_129174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_129174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129174 prefixEnd_129174 := by exact prefixLift 129174
  have htrace : WordTrace (prefixWord ++ tailWord_129174) baseStart_129174 baseEnd_129174 := by
    simpa [prefixWord, tailWord_129174, baseEnd_129174] using wordTrace_append hprefix tailTrace_129174
  have hstable : (prefixWord ++ tailWord_129174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129174).length < 2 ^ (prefixWord ++ tailWord_129174).sum := by decide
  have hdescent : baseEnd_129174 < baseStart_129174 := by decide
  rcases family_descends (prefixWord ++ tailWord_129174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129175 : List Nat := [1, 1, 3, 3, 4, 1, 1, 4, 2]
def baseStart_129175 : Nat := 118140960795 + 129175 * 2 ^ 59
def prefixEnd_129175 : Nat := 4983230072969 + 3 ^ 40 * 129175 * 2
def baseEnd_129175 : Nat := 58958989817455409705281

theorem tailTrace_129175 : CollatzResearch.WordTrace tailWord_129175 prefixEnd_129175 58958989817455409705281 := by
  unfold tailWord_129175
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711399307028511178716979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3140932871352340785811319 4711399307028511178716979)
  ·
    refine ⟨7067098960542766768075469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4711399307028511178716979 7067098960542766768075469)
    ·
      refine ⟨2650162110203537538028301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7067098960542766768075469 2650162110203537538028301)
      ·
        refine ⟨993810791326326576760613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2650162110203537538028301 993810791326326576760613)
        ·
          refine ⟨186339523373686233142615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 993810791326326576760613 186339523373686233142615)
          ·
            refine ⟨279509285060529349713923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186339523373686233142615 279509285060529349713923)
            ·
              refine ⟨419263927590794024570885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279509285060529349713923 419263927590794024570885)
              ·
                refine ⟨78611986423273879607041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419263927590794024570885 78611986423273879607041)
                ·
                  refine ⟨58958989817455409705281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78611986423273879607041 58958989817455409705281)
                  ·
                    rfl

theorem cell20_129175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 2].length) (baseStart_129175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129175 prefixEnd_129175 := by exact prefixLift 129175
  have htrace : WordTrace (prefixWord ++ tailWord_129175) baseStart_129175 baseEnd_129175 := by
    simpa [prefixWord, tailWord_129175, baseEnd_129175] using wordTrace_append hprefix tailTrace_129175
  have hstable : (prefixWord ++ tailWord_129175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129175).length < 2 ^ (prefixWord ++ tailWord_129175).sum := by decide
  have hdescent : baseEnd_129175 < baseStart_129175 := by decide
  rcases family_descends (prefixWord ++ tailWord_129175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129231 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_129231 : Nat := 118140960795 + 129231 * 2 ^ 59
def prefixEnd_129231 : Nat := 4983230072969 + 3 ^ 40 * 129231 * 2
def baseEnd_129231 : Nat := 58984549743368103838385

theorem tailTrace_129231 : CollatzResearch.WordTrace tailWord_129231 prefixEnd_129231 58984549743368103838385 := by
  unfold tailWord_129231
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713441794825632742755547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3142294529883755161837031 4713441794825632742755547)
  ·
    refine ⟨7070162692238449114133321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4713441794825632742755547 7070162692238449114133321)
    ·
      refine ⟨5302622019178836835599991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7070162692238449114133321 5302622019178836835599991)
      ·
        refine ⟨7953933028768255253399987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302622019178836835599991 7953933028768255253399987)
        ·
          refine ⟨11930899543152382880099981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7953933028768255253399987 11930899543152382880099981)
          ·
            refine ⟨4474087328682143580037493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11930899543152382880099981 4474087328682143580037493)
            ·
              refine ⟨419445687063950960628515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4474087328682143580037493 419445687063950960628515)
              ·
                refine ⟨629168530595926440942773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419445687063950960628515 629168530595926440942773)
                ·
                  refine ⟨58984549743368103838385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 629168530595926440942773 58984549743368103838385)
                  ·
                    rfl

theorem cell20_129231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_129231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129231 prefixEnd_129231 := by exact prefixLift 129231
  have htrace : WordTrace (prefixWord ++ tailWord_129231) baseStart_129231 baseEnd_129231 := by
    simpa [prefixWord, tailWord_129231, baseEnd_129231] using wordTrace_append hprefix tailTrace_129231
  have hstable : (prefixWord ++ tailWord_129231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129231).length < 2 ^ (prefixWord ++ tailWord_129231).sum := by decide
  have hdescent : baseEnd_129231 < baseStart_129231 := by decide
  rcases family_descends (prefixWord ++ tailWord_129231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129234 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_129234 : Nat := 118140960795 + 129234 * 2 ^ 59
def prefixEnd_129234 : Nat := 4983230072969 + 3 ^ 40 * 129234 * 2
def baseEnd_129234 : Nat := 58985919025113426738373

theorem tailTrace_129234 : CollatzResearch.WordTrace tailWord_129234 prefixEnd_129234 58985919025113426738373 := by
  unfold tailWord_129234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1178387803453691063778689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3142367475876509503409837 1178387803453691063778689)
  ·
    refine ⟨883790852590268297834017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1178387803453691063778689 883790852590268297834017)
    ·
      refine ⟨662843139442701223375513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 883790852590268297834017 662843139442701223375513)
      ·
        refine ⟨497132354582025917531635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662843139442701223375513 497132354582025917531635)
        ·
          refine ⟨745698531873038876297453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497132354582025917531635 745698531873038876297453)
          ·
            refine ⟨279636949452389578611545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 745698531873038876297453 279636949452389578611545)
            ·
              refine ⟨209727712089292183958659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279636949452389578611545 209727712089292183958659)
              ·
                refine ⟨314591568133938275937989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209727712089292183958659 314591568133938275937989)
                ·
                  refine ⟨58985919025113426738373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314591568133938275937989 58985919025113426738373)
                  ·
                    rfl

theorem cell20_129234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_129234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129234 prefixEnd_129234 := by exact prefixLift 129234
  have htrace : WordTrace (prefixWord ++ tailWord_129234) baseStart_129234 baseEnd_129234 := by
    simpa [prefixWord, tailWord_129234, baseEnd_129234] using wordTrace_append hprefix tailTrace_129234
  have hstable : (prefixWord ++ tailWord_129234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129234).length < 2 ^ (prefixWord ++ tailWord_129234).sum := by decide
  have hdescent : baseEnd_129234 < baseStart_129234 := by decide
  rcases family_descends (prefixWord ++ tailWord_129234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129289 : List Nat := [1, 2, 1, 1, 3, 5, 3, 2, 2]
def baseStart_129289 : Nat := 118140960795 + 129289 * 2 ^ 59
def prefixEnd_129289 : Nat := 4983230072969 + 3 ^ 40 * 129289 * 2
def baseEnd_129289 : Nat := 59011022523777679904815

theorem tailTrace_129289 : CollatzResearch.WordTrace tailWord_129289 prefixEnd_129289 59011022523777679904815 := by
  unfold tailWord_129289
  simp only [CollatzResearch.WordTrace]
  refine ⟨4715557228615508648366921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3143704819077005765577947 4715557228615508648366921)
  ·
    refine ⟨3536667921461631486275191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4715557228615508648366921 3536667921461631486275191)
    ·
      refine ⟨5305001882192447229412787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3536667921461631486275191 5305001882192447229412787)
      ·
        refine ⟨7957502823288670844119181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5305001882192447229412787 7957502823288670844119181)
        ·
          refine ⟨2984063558733251566544693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7957502823288670844119181 2984063558733251566544693)
          ·
            refine ⟨279755958631242334363565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2984063558733251566544693 279755958631242334363565)
            ·
              refine ⟨104908484486715875386337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279755958631242334363565 104908484486715875386337)
              ·
                refine ⟨78681363365036906539753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104908484486715875386337 78681363365036906539753)
                ·
                  refine ⟨59011022523777679904815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78681363365036906539753 59011022523777679904815)
                  ·
                    rfl

theorem cell20_129289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_129289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129289 prefixEnd_129289 := by exact prefixLift 129289
  have htrace : WordTrace (prefixWord ++ tailWord_129289) baseStart_129289 baseEnd_129289 := by
    simpa [prefixWord, tailWord_129289, baseEnd_129289] using wordTrace_append hprefix tailTrace_129289
  have hstable : (prefixWord ++ tailWord_129289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129289).length < 2 ^ (prefixWord ++ tailWord_129289).sum := by decide
  have hdescent : baseEnd_129289 < baseStart_129289 := by decide
  rcases family_descends (prefixWord ++ tailWord_129289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129303 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 3]
def baseStart_129303 : Nat := 118140960795 + 129303 * 2 ^ 59
def prefixEnd_129303 : Nat := 4983230072969 + 3 ^ 40 * 129303 * 2
def baseEnd_129303 : Nat := 59017412505255853438091

theorem tailTrace_129303 : CollatzResearch.WordTrace tailWord_129303 prefixEnd_129303 59017412505255853438091 := by
  unfold tailWord_129303
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716067850564789039376563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3144045233709859359584375 4716067850564789039376563)
  ·
    refine ⟨7074101775847183559064845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4716067850564789039376563 7074101775847183559064845)
    ·
      refine ⟨2652788165942693834649317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7074101775847183559064845 2652788165942693834649317)
      ·
        refine ⟨497397781114255093996747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2652788165942693834649317 497397781114255093996747)
        ·
          refine ⟨746096671671382640995121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497397781114255093996747 746096671671382640995121)
          ·
            refine ⟨559572503753536980746341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746096671671382640995121 559572503753536980746341)
            ·
              refine ⟨104919844453788183889939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 559572503753536980746341 104919844453788183889939)
              ·
                refine ⟨157379766680682275834909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104919844453788183889939 157379766680682275834909)
                ·
                  refine ⟨59017412505255853438091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157379766680682275834909 59017412505255853438091)
                  ·
                    rfl

theorem cell20_129303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 3].length) (baseStart_129303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129303 prefixEnd_129303 := by exact prefixLift 129303
  have htrace : WordTrace (prefixWord ++ tailWord_129303) baseStart_129303 baseEnd_129303 := by
    simpa [prefixWord, tailWord_129303, baseEnd_129303] using wordTrace_append hprefix tailTrace_129303
  have hstable : (prefixWord ++ tailWord_129303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129303).length < 2 ^ (prefixWord ++ tailWord_129303).sum := by decide
  have hdescent : baseEnd_129303 < baseStart_129303 := by decide
  rcases family_descends (prefixWord ++ tailWord_129303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129359 : List Nat := [1, 1, 2, 1, 1, 2, 1, 11]
def baseStart_129359 : Nat := 118140960795 + 129359 * 2 ^ 59
def prefixEnd_129359 : Nat := 4983230072969 + 3 ^ 40 * 129359 * 2
def baseEnd_129359 : Nat := 19680990810389515857065

theorem tailTrace_129359 : CollatzResearch.WordTrace tailWord_129359 prefixEnd_129359 19680990810389515857065 := by
  unfold tailWord_129359
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718110338361910603415131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3145406892241273735610087 4718110338361910603415131)
  ·
    refine ⟨7077165507542865905122697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4718110338361910603415131 7077165507542865905122697)
    ·
      refine ⟨5307874130657149428842023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7077165507542865905122697 5307874130657149428842023)
      ·
        refine ⟨7961811195985724143263035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5307874130657149428842023 7961811195985724143263035)
        ·
          refine ⟨11942716793978586214894553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7961811195985724143263035 11942716793978586214894553)
          ·
            refine ⟨8957037595483939661170915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11942716793978586214894553 8957037595483939661170915)
            ·
              refine ⟨13435556393225909491756373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8957037595483939661170915 13435556393225909491756373)
              ·
                refine ⟨19680990810389515857065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 13435556393225909491756373 19680990810389515857065)
                ·
                  rfl

theorem cell20_129359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_129359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129359 prefixEnd_129359 := by exact prefixLift 129359
  have htrace : WordTrace (prefixWord ++ tailWord_129359) baseStart_129359 baseEnd_129359 := by
    simpa [prefixWord, tailWord_129359, baseEnd_129359] using wordTrace_append hprefix tailTrace_129359
  have hstable : (prefixWord ++ tailWord_129359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129359).length < 2 ^ (prefixWord ++ tailWord_129359).sum := by decide
  have hdescent : baseEnd_129359 < baseStart_129359 := by decide
  rcases family_descends (prefixWord ++ tailWord_129359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129362 : List Nat := [3, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_129362 : Nat := 118140960795 + 129362 * 2 ^ 59
def prefixEnd_129362 : Nat := 4983230072969 + 3 ^ 40 * 129362 * 2
def baseEnd_129362 : Nat := 59044341712913870471183

theorem tailTrace_129362 : CollatzResearch.WordTrace tailWord_129362 prefixEnd_129362 59044341712913870471183 := by
  unfold tailWord_129362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179554939337760528943585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3145479838234028077182893 1179554939337760528943585)
  ·
    refine ⟨884666204503320396707689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1179554939337760528943585 884666204503320396707689)
    ·
      refine ⟨663499653377490297530767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 884666204503320396707689 663499653377490297530767)
      ·
        refine ⟨995249480066235446296151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663499653377490297530767 995249480066235446296151)
        ·
          refine ⟨1492874220099353169444227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995249480066235446296151 1492874220099353169444227)
          ·
            refine ⟨2239311330149029754166341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492874220099353169444227 2239311330149029754166341)
            ·
              refine ⟨419870874402943078906189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2239311330149029754166341 419870874402943078906189)
              ·
                refine ⟨157451577901103654589821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419870874402943078906189 157451577901103654589821)
                ·
                  refine ⟨59044341712913870471183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157451577901103654589821 59044341712913870471183)
                  ·
                    rfl

theorem cell20_129362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_129362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129362 prefixEnd_129362 := by exact prefixLift 129362
  have htrace : WordTrace (prefixWord ++ tailWord_129362) baseStart_129362 baseEnd_129362 := by
    simpa [prefixWord, tailWord_129362, baseEnd_129362] using wordTrace_append hprefix tailTrace_129362
  have hstable : (prefixWord ++ tailWord_129362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129362).length < 2 ^ (prefixWord ++ tailWord_129362).sum := by decide
  have hdescent : baseEnd_129362 < baseStart_129362 := by decide
  rcases family_descends (prefixWord ++ tailWord_129362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129417 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 3]
def baseStart_129417 : Nat := 118140960795 + 129417 * 2 ^ 59
def prefixEnd_129417 : Nat := 4983230072969 + 3 ^ 40 * 129417 * 2
def baseEnd_129417 : Nat := 59069445211578123637625

theorem tailTrace_129417 : CollatzResearch.WordTrace tailWord_129417 prefixEnd_129417 59069445211578123637625 := by
  unfold tailWord_129417
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720225772151786509026505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3146817181434524339351003 4720225772151786509026505)
  ·
    refine ⟨3540169329113839881769879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4720225772151786509026505 3540169329113839881769879)
    ·
      refine ⟨5310253993670759822654819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3540169329113839881769879 5310253993670759822654819)
      ·
        refine ⟨7965380990506139733982229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5310253993670759822654819 7965380990506139733982229)
        ·
          refine ⟨373377233929975300030417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7965380990506139733982229 373377233929975300030417)
          ·
            refine ⟨280032925447481475022813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373377233929975300030417 280032925447481475022813)
            ·
              refine ⟨105012347042805553133555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280032925447481475022813 105012347042805553133555)
              ·
                refine ⟨157518520564208329700333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105012347042805553133555 157518520564208329700333)
                ·
                  refine ⟨59069445211578123637625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157518520564208329700333 59069445211578123637625)
                  ·
                    rfl

theorem cell20_129417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_129417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129417 prefixEnd_129417 := by exact prefixLift 129417
  have htrace : WordTrace (prefixWord ++ tailWord_129417) baseStart_129417 baseEnd_129417 := by
    simpa [prefixWord, tailWord_129417, baseEnd_129417] using wordTrace_append hprefix tailTrace_129417
  have hstable : (prefixWord ++ tailWord_129417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129417).length < 2 ^ (prefixWord ++ tailWord_129417).sum := by decide
  have hdescent : baseEnd_129417 < baseStart_129417 := by decide
  rcases family_descends (prefixWord ++ tailWord_129417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129514 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_129514 : Nat := 118140960795 + 129514 * 2 ^ 59
def prefixEnd_129514 : Nat := 4983230072969 + 3 ^ 40 * 129514 * 2
def baseEnd_129514 : Nat := 59113718654676897403895

theorem tailTrace_129514 : CollatzResearch.WordTrace tailWord_129514 prefixEnd_129514 59113718654676897403895 := by
  unfold tailWord_129514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180940913200093018826899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3149175768533581383538397 1180940913200093018826899)
  ·
    refine ⟨1771411369800139528240349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1180940913200093018826899 1771411369800139528240349)
    ·
      refine ⟨664279263675052323090131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1771411369800139528240349 664279263675052323090131)
      ·
        refine ⟨996418895512578484635197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664279263675052323090131 996418895512578484635197)
        ·
          refine ⟨373657085817216931738199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 996418895512578484635197 373657085817216931738199)
          ·
            refine ⟨560485628725825397607299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373657085817216931738199 560485628725825397607299)
            ·
              refine ⟨840728443088738096410949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560485628725825397607299 840728443088738096410949)
              ·
                refine ⟨157636583079138393077053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 840728443088738096410949 157636583079138393077053)
                ·
                  refine ⟨59113718654676897403895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157636583079138393077053 59113718654676897403895)
                  ·
                    rfl

theorem cell20_129514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_129514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129514 prefixEnd_129514 := by exact prefixLift 129514
  have htrace : WordTrace (prefixWord ++ tailWord_129514) baseStart_129514 baseEnd_129514 := by
    simpa [prefixWord, tailWord_129514, baseEnd_129514] using wordTrace_append hprefix tailTrace_129514
  have hstable : (prefixWord ++ tailWord_129514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129514).length < 2 ^ (prefixWord ++ tailWord_129514).sum := by decide
  have hdescent : baseEnd_129514 < baseStart_129514 := by decide
  rcases family_descends (prefixWord ++ tailWord_129514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129517 : List Nat := [1, 5, 1, 3, 1, 2, 1, 4, 2]
def baseStart_129517 : Nat := 118140960795 + 129517 * 2 ^ 59
def prefixEnd_129517 : Nat := 4983230072969 + 3 ^ 40 * 129517 * 2
def baseEnd_129517 : Nat := 59115087936422220303883

theorem tailTrace_129517 : CollatzResearch.WordTrace tailWord_129517 prefixEnd_129517 59115087936422220303883 := by
  unfold tailWord_129517
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723873071789503587666805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3149248714526335725111203 4723873071789503587666805)
  ·
    refine ⟨442863100480265961343763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4723873071789503587666805 442863100480265961343763)
    ·
      refine ⟨664294650720398942015645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442863100480265961343763 664294650720398942015645)
      ·
        refine ⟨249110494020149603255867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664294650720398942015645 249110494020149603255867)
        ·
          refine ⟨373665741030224404883801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249110494020149603255867 373665741030224404883801)
          ·
            refine ⟨280249305772668303662851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373665741030224404883801 280249305772668303662851)
            ·
              refine ⟨420373958659002455494277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280249305772668303662851 420373958659002455494277)
              ·
                refine ⟨78820117248562960405177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420373958659002455494277 78820117248562960405177)
                ·
                  refine ⟨59115087936422220303883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78820117248562960405177 59115087936422220303883)
                  ·
                    rfl

theorem cell20_129517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_129517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129517 prefixEnd_129517 := by exact prefixLift 129517
  have htrace : WordTrace (prefixWord ++ tailWord_129517) baseStart_129517 baseEnd_129517 := by
    simpa [prefixWord, tailWord_129517, baseEnd_129517] using wordTrace_append hprefix tailTrace_129517
  have hstable : (prefixWord ++ tailWord_129517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129517).length < 2 ^ (prefixWord ++ tailWord_129517).sum := by decide
  have hdescent : baseEnd_129517 < baseStart_129517 := by decide
  rcases family_descends (prefixWord ++ tailWord_129517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129535 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 3]
def baseStart_129535 : Nat := 118140960795 + 129535 * 2 ^ 59
def prefixEnd_129535 : Nat := 4983230072969 + 3 ^ 40 * 129535 * 2
def baseEnd_129535 : Nat := 59123303626894157703809

theorem tailTrace_129535 : CollatzResearch.WordTrace tailWord_129535 prefixEnd_129535 59123303626894157703809 := by
  unfold tailWord_129535
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724529585724292661822059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3149686390482861774548039 4724529585724292661822059)
  ·
    refine ⟨7086794378586438992733089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4724529585724292661822059 7086794378586438992733089)
    ·
      refine ⟨5315095783939829244549817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7086794378586438992733089 5315095783939829244549817)
      ·
        refine ⟨3986321837954871933412363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5315095783939829244549817 3986321837954871933412363)
        ·
          refine ⟨5979482756932307900118545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3986321837954871933412363 5979482756932307900118545)
          ·
            refine ⟨4484612067699230925088909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5979482756932307900118545 4484612067699230925088909)
            ·
              refine ⟨1681729525387211596908341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4484612067699230925088909 1681729525387211596908341)
              ·
                refine ⟨157662143005051087210157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1681729525387211596908341 157662143005051087210157)
                ·
                  refine ⟨59123303626894157703809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157662143005051087210157 59123303626894157703809)
                  ·
                    rfl

theorem cell20_129535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_129535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129535 prefixEnd_129535 := by exact prefixLift 129535
  have htrace : WordTrace (prefixWord ++ tailWord_129535) baseStart_129535 baseEnd_129535 := by
    simpa [prefixWord, tailWord_129535, baseEnd_129535] using wordTrace_append hprefix tailTrace_129535
  have hstable : (prefixWord ++ tailWord_129535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129535).length < 2 ^ (prefixWord ++ tailWord_129535).sum := by decide
  have hdescent : baseEnd_129535 < baseStart_129535 := by decide
  rcases family_descends (prefixWord ++ tailWord_129535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129576 : List Nat := [2, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_129576 : Nat := 118140960795 + 129576 * 2 ^ 59
def prefixEnd_129576 : Nat := 4983230072969 + 3 ^ 40 * 129576 * 2
def baseEnd_129576 : Nat := 59142017144080237336975

theorem tailTrace_129576 : CollatzResearch.WordTrace tailWord_129576 prefixEnd_129576 59142017144080237336975 := by
  unfold tailWord_129576
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363012489287878332032291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3150683319050504442709721 2363012489287878332032291)
  ·
    refine ⟨3544518733931817498048437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2363012489287878332032291 3544518733931817498048437)
    ·
      refine ⟨332298631306107890442041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3544518733931817498048437 332298631306107890442041)
      ·
        refine ⟨249223973479580917831531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332298631306107890442041 249223973479580917831531)
        ·
          refine ⟨373835960219371376747297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249223973479580917831531 373835960219371376747297)
          ·
            refine ⟨280376970164528532560473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373835960219371376747297 280376970164528532560473)
            ·
              refine ⟨210282727623396399420355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280376970164528532560473 210282727623396399420355)
              ·
                refine ⟨315424091435094599130533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210282727623396399420355 315424091435094599130533)
                ·
                  refine ⟨59142017144080237336975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315424091435094599130533 59142017144080237336975)
                  ·
                    rfl

theorem cell20_129576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_129576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129576 prefixEnd_129576 := by exact prefixLift 129576
  have htrace : WordTrace (prefixWord ++ tailWord_129576) baseStart_129576 baseEnd_129576 := by
    simpa [prefixWord, tailWord_129576, baseEnd_129576] using wordTrace_append hprefix tailTrace_129576
  have hstable : (prefixWord ++ tailWord_129576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129576).length < 2 ^ (prefixWord ++ tailWord_129576).sum := by decide
  have hdescent : baseEnd_129576 < baseStart_129576 := by decide
  rcases family_descends (prefixWord ++ tailWord_129576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129587 : List Nat := [1, 1, 1, 2, 4, 2, 2, 7]
def baseStart_129587 : Nat := 118140960795 + 129587 * 2 ^ 59
def prefixEnd_129587 : Nat := 4983230072969 + 3 ^ 40 * 129587 * 2
def baseEnd_129587 : Nat := 19715679281271029323421

theorem tailTrace_129587 : CollatzResearch.WordTrace tailWord_129587 prefixEnd_129587 19715679281271029323421 := by
  unfold tailWord_129587
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726426181535905542715015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3150950787690603695143343 4726426181535905542715015)
  ·
    refine ⟨7089639272303858314072523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4726426181535905542715015 7089639272303858314072523)
    ·
      refine ⟨10634458908455787471108785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7089639272303858314072523 10634458908455787471108785)
      ·
        refine ⟨7975844181341840603331589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10634458908455787471108785 7975844181341840603331589)
        ·
          refine ⟨1495470784001595113124673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7975844181341840603331589 1495470784001595113124673)
          ·
            refine ⟨1121603088001196334843505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495470784001595113124673 1121603088001196334843505)
            ·
              refine ⟨841202316000897251132629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121603088001196334843505 841202316000897251132629)
              ·
                refine ⟨19715679281271029323421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 841202316000897251132629 19715679281271029323421)
                ·
                  rfl

theorem cell20_129587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_129587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129587 prefixEnd_129587 := by exact prefixLift 129587
  have htrace : WordTrace (prefixWord ++ tailWord_129587) baseStart_129587 baseEnd_129587 := by
    simpa [prefixWord, tailWord_129587, baseEnd_129587] using wordTrace_append hprefix tailTrace_129587
  have hstable : (prefixWord ++ tailWord_129587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129587).length < 2 ^ (prefixWord ++ tailWord_129587).sum := by decide
  have hdescent : baseEnd_129587 < baseStart_129587 := by decide
  rcases family_descends (prefixWord ++ tailWord_129587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129597 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_129597 : Nat := 118140960795 + 129597 * 2 ^ 59
def prefixEnd_129597 : Nat := 4983230072969 + 3 ^ 40 * 129597 * 2
def baseEnd_129597 : Nat := 59151602116297497636889

theorem tailTrace_129597 : CollatzResearch.WordTrace tailWord_129597 prefixEnd_129597 59151602116297497636889 := by
  unfold tailWord_129597
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726790911499677250579045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3151193940999784833719363 4726790911499677250579045)
  ·
    refine ⟨886273295906189484483571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4726790911499677250579045 886273295906189484483571)
    ·
      refine ⟨1329409943859284226725357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886273295906189484483571 1329409943859284226725357)
      ·
        refine ⟨498528728947231585022009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1329409943859284226725357 498528728947231585022009)
        ·
          refine ⟨373896546710423688766507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498528728947231585022009 373896546710423688766507)
          ·
            refine ⟨560844820065635533149761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373896546710423688766507 560844820065635533149761)
            ·
              refine ⟨420633615049226649862321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560844820065635533149761 420633615049226649862321)
              ·
                refine ⟨315475211286919987396741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420633615049226649862321 315475211286919987396741)
                ·
                  refine ⟨59151602116297497636889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315475211286919987396741 59151602116297497636889)
                  ·
                    rfl

theorem cell20_129597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_129597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129597 prefixEnd_129597 := by exact prefixLift 129597
  have htrace : WordTrace (prefixWord ++ tailWord_129597) baseStart_129597 baseEnd_129597 := by
    simpa [prefixWord, tailWord_129597, baseEnd_129597] using wordTrace_append hprefix tailTrace_129597
  have hstable : (prefixWord ++ tailWord_129597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129597).length < 2 ^ (prefixWord ++ tailWord_129597).sum := by decide
  have hdescent : baseEnd_129597 < baseStart_129597 := by decide
  rcases family_descends (prefixWord ++ tailWord_129597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129614 : List Nat := [4, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_129614 : Nat := 118140960795 + 129614 * 2 ^ 59
def prefixEnd_129614 : Nat := 4983230072969 + 3 ^ 40 * 129614 * 2
def baseEnd_129614 : Nat := 59159361379520994070153

theorem tailTrace_129614 : CollatzResearch.WordTrace tailWord_129614 prefixEnd_129614 59159361379520994070153 := by
  unfold tailWord_129614
  simp only [CollatzResearch.WordTrace]
  refine ⟨590926369054761144243487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3151607301625392769298597 590926369054761144243487)
  ·
    refine ⟨886389553582141716365231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 590926369054761144243487 886389553582141716365231)
    ·
      refine ⟨1329584330373212574547847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886389553582141716365231 1329584330373212574547847)
      ·
        refine ⟨1994376495559818861821771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329584330373212574547847 1994376495559818861821771)
        ·
          refine ⟨2991564743339728292732657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1994376495559818861821771 2991564743339728292732657)
          ·
            refine ⟨2243673557504796219549493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2991564743339728292732657 2243673557504796219549493)
            ·
              refine ⟨210344396016074645582765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2243673557504796219549493 210344396016074645582765)
              ·
                refine ⟨78879148506027992093537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210344396016074645582765 78879148506027992093537)
                ·
                  refine ⟨59159361379520994070153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78879148506027992093537 59159361379520994070153)
                  ·
                    rfl

theorem cell20_129614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_129614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129614 prefixEnd_129614 := by exact prefixLift 129614
  have htrace : WordTrace (prefixWord ++ tailWord_129614) baseStart_129614 baseEnd_129614 := by
    simpa [prefixWord, tailWord_129614, baseEnd_129614] using wordTrace_append hprefix tailTrace_129614
  have hstable : (prefixWord ++ tailWord_129614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129614).length < 2 ^ (prefixWord ++ tailWord_129614).sum := by decide
  have hdescent : baseEnd_129614 < baseStart_129614 := by decide
  rcases family_descends (prefixWord ++ tailWord_129614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129642 : List Nat := [3, 1, 3, 2, 1, 1, 4, 5]
def baseStart_129642 : Nat := 118140960795 + 129642 * 2 ^ 59
def prefixEnd_129642 : Nat := 4983230072969 + 3 ^ 40 * 129642 * 2
def baseEnd_129642 : Nat := 19724047114159113712235

theorem tailTrace_129642 : CollatzResearch.WordTrace tailWord_129642 prefixEnd_129642 19724047114159113712235 := by
  unfold tailWord_129642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1182108049084162483991795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3152288130891099957311453 1182108049084162483991795)
  ·
    refine ⟨1773162073626243725987693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1182108049084162483991795 1773162073626243725987693)
    ·
      refine ⟨664935777609841397245385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1773162073626243725987693 664935777609841397245385)
      ·
        refine ⟨498701833207381047934039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664935777609841397245385 498701833207381047934039)
        ·
          refine ⟨748052749811071571901059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498701833207381047934039 748052749811071571901059)
          ·
            refine ⟨1122079124716607357851589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748052749811071571901059 1122079124716607357851589)
            ·
              refine ⟨210389835884363879597173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1122079124716607357851589 210389835884363879597173)
              ·
                refine ⟨19724047114159113712235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210389835884363879597173 19724047114159113712235)
                ·
                  rfl

theorem cell20_129642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_129642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129642 prefixEnd_129642 := by exact prefixLift 129642
  have htrace : WordTrace (prefixWord ++ tailWord_129642) baseStart_129642 baseEnd_129642 := by
    simpa [prefixWord, tailWord_129642, baseEnd_129642] using wordTrace_append hprefix tailTrace_129642
  have hstable : (prefixWord ++ tailWord_129642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129642).length < 2 ^ (prefixWord ++ tailWord_129642).sum := by decide
  have hdescent : baseEnd_129642 < baseStart_129642 := by decide
  rcases family_descends (prefixWord ++ tailWord_129642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129645 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 3]
def baseStart_129645 : Nat := 118140960795 + 129645 * 2 ^ 59
def prefixEnd_129645 : Nat := 4983230072969 + 3 ^ 40 * 129645 * 2
def baseEnd_129645 : Nat := 59173510624222664036693

theorem tailTrace_129645 : CollatzResearch.WordTrace tailWord_129645 prefixEnd_129645 59173510624222664036693 := by
  unfold tailWord_129645
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728541615325781448326389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3152361076883854298884259 4728541615325781448326389)
  ·
    refine ⟨443300776436792010780599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4728541615325781448326389 443300776436792010780599)
    ·
      refine ⟨664951164655188016170899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443300776436792010780599 664951164655188016170899)
      ·
        refine ⟨997426746982782024256349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664951164655188016170899 997426746982782024256349)
        ·
          refine ⟨374035030118543259096131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 997426746982782024256349 374035030118543259096131)
          ·
            refine ⟨561052545177814888644197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374035030118543259096131 561052545177814888644197)
            ·
              refine ⟨105197352220840291620787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 561052545177814888644197 105197352220840291620787)
              ·
                refine ⟨157796028331260437431181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105197352220840291620787 157796028331260437431181)
                ·
                  refine ⟨59173510624222664036693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157796028331260437431181 59173510624222664036693)
                  ·
                    rfl

theorem cell20_129645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_129645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129645 prefixEnd_129645 := by exact prefixLift 129645
  have htrace : WordTrace (prefixWord ++ tailWord_129645) baseStart_129645 baseEnd_129645 := by
    simpa [prefixWord, tailWord_129645, baseEnd_129645] using wordTrace_append hprefix tailTrace_129645
  have hstable : (prefixWord ++ tailWord_129645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129645).length < 2 ^ (prefixWord ++ tailWord_129645).sum := by decide
  have hdescent : baseEnd_129645 < baseStart_129645 := by decide
  rcases family_descends (prefixWord ++ tailWord_129645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129673 : List Nat := [1, 2, 1, 1, 4, 1, 1, 7, 2]
def baseStart_129673 : Nat := 118140960795 + 129673 * 2 ^ 59
def prefixEnd_129673 : Nat := 4983230072969 + 3 ^ 40 * 129673 * 2
def baseEnd_129673 : Nat := 59186290587179011103245

theorem tailTrace_129673 : CollatzResearch.WordTrace tailWord_129673 prefixEnd_129673 59186290587179011103245 := by
  unfold tailWord_129673
  simp only [CollatzResearch.WordTrace]
  refine ⟨4729562859224342230345673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3153041906149561486897115 4729562859224342230345673)
  ·
    refine ⟨3547172144418256672759255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4729562859224342230345673 3547172144418256672759255)
    ·
      refine ⟨5320758216627385009138883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3547172144418256672759255 5320758216627385009138883)
      ·
        refine ⟨7981137324941077513708325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320758216627385009138883 7981137324941077513708325)
        ·
          refine ⟨1496463248426452033820311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7981137324941077513708325 1496463248426452033820311)
          ·
            refine ⟨2244694872639678050730467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496463248426452033820311 2244694872639678050730467)
            ·
              refine ⟨3367042308959517076095701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244694872639678050730467 3367042308959517076095701)
              ·
                refine ⟨78915054116238681470993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3367042308959517076095701 78915054116238681470993)
                ·
                  refine ⟨59186290587179011103245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78915054116238681470993 59186290587179011103245)
                  ·
                    rfl

theorem cell20_129673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_129673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129673 prefixEnd_129673 := by exact prefixLift 129673
  have htrace : WordTrace (prefixWord ++ tailWord_129673) baseStart_129673 baseEnd_129673 := by
    simpa [prefixWord, tailWord_129673, baseEnd_129673] using wordTrace_append hprefix tailTrace_129673
  have hstable : (prefixWord ++ tailWord_129673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129673).length < 2 ^ (prefixWord ++ tailWord_129673).sum := by decide
  have hdescent : baseEnd_129673 < baseStart_129673 := by decide
  rcases family_descends (prefixWord ++ tailWord_129673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129697 : List Nat := [1, 2, 3, 3, 3, 2, 1, 5]
def baseStart_129697 : Nat := 118140960795 + 129697 * 2 ^ 59
def prefixEnd_129697 : Nat := 4983230072969 + 3 ^ 40 * 129697 * 2
def baseEnd_129697 : Nat := 19732414947047198101049

theorem tailTrace_129697 : CollatzResearch.WordTrace tailWord_129697 prefixEnd_129697 19732414947047198101049 := by
  unfold tailWord_129697
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730438211137394329219345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3153625474091596219479563 4730438211137394329219345)
  ·
    refine ⟨3547828658353045746914509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4730438211137394329219345 3547828658353045746914509)
    ·
      refine ⟨1330435746882392155092941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3547828658353045746914509 1330435746882392155092941)
      ·
        refine ⟨498913405080897058159853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1330435746882392155092941 498913405080897058159853)
        ·
          refine ⟨187092526905336396809945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498913405080897058159853 187092526905336396809945)
          ·
            refine ⟨140319395179002297607459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187092526905336396809945 140319395179002297607459)
            ·
              refine ⟨210479092768503446411189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140319395179002297607459 210479092768503446411189)
              ·
                refine ⟨19732414947047198101049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210479092768503446411189 19732414947047198101049)
                ·
                  rfl

theorem cell20_129697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 5].length) (baseStart_129697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129697 prefixEnd_129697 := by exact prefixLift 129697
  have htrace : WordTrace (prefixWord ++ tailWord_129697) baseStart_129697 baseEnd_129697 := by
    simpa [prefixWord, tailWord_129697, baseEnd_129697] using wordTrace_append hprefix tailTrace_129697
  have hstable : (prefixWord ++ tailWord_129697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129697).length < 2 ^ (prefixWord ++ tailWord_129697).sum := by decide
  have hdescent : baseEnd_129697 < baseStart_129697 := by decide
  rcases family_descends (prefixWord ++ tailWord_129697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129728 : List Nat := [2, 1, 1, 2, 4, 3, 2, 3, 2]
def baseStart_129728 : Nat := 118140960795 + 129728 * 2 ^ 59
def prefixEnd_129728 : Nat := 4983230072969 + 3 ^ 40 * 129728 * 2
def baseEnd_129728 : Nat := 59211394085843264269687

theorem tailTrace_129728 : CollatzResearch.WordTrace tailWord_129728 prefixEnd_129728 59211394085843264269687 := by
  unfold tailWord_129728
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365784437012543311798919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3154379249350057749065225 2365784437012543311798919)
  ·
    refine ⟨3548676655518814967698379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2365784437012543311798919 3548676655518814967698379)
    ·
      refine ⟨5323014983278222451547569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3548676655518814967698379 5323014983278222451547569)
      ·
        refine ⟨3992261237458666838660677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5323014983278222451547569 3992261237458666838660677)
        ·
          refine ⟨748548982023500032248877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3992261237458666838660677 748548982023500032248877)
          ·
            refine ⟨280705868258812512093329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 748548982023500032248877 280705868258812512093329)
            ·
              refine ⟨210529401194109384069997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280705868258812512093329 210529401194109384069997)
              ·
                refine ⟨78948525447791019026249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210529401194109384069997 78948525447791019026249)
                ·
                  refine ⟨59211394085843264269687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78948525447791019026249 59211394085843264269687)
                  ·
                    rfl

theorem cell20_129728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_129728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129728 prefixEnd_129728 := by exact prefixLift 129728
  have htrace : WordTrace (prefixWord ++ tailWord_129728) baseStart_129728 baseEnd_129728 := by
    simpa [prefixWord, tailWord_129728, baseEnd_129728] using wordTrace_append hprefix tailTrace_129728
  have hstable : (prefixWord ++ tailWord_129728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129728).length < 2 ^ (prefixWord ++ tailWord_129728).sum := by decide
  have hdescent : baseEnd_129728 < baseStart_129728 := by decide
  rcases family_descends (prefixWord ++ tailWord_129728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129734 : List Nat := [6, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_129734 : Nat := 118140960795 + 129734 * 2 ^ 59
def prefixEnd_129734 : Nat := 4983230072969 + 3 ^ 40 * 129734 * 2
def baseEnd_129734 : Nat := 59214132649333910069663

theorem tailTrace_129734 : CollatzResearch.WordTrace tailWord_129734 prefixEnd_129734 59214132649333910069663 := by
  unfold tailWord_129734
  simp only [CollatzResearch.WordTrace]
  refine ⟨147868366000104676509883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3154525141335566432210837 147868366000104676509883)
  ·
    refine ⟨221802549000157014764825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147868366000104676509883 221802549000157014764825)
    ·
      refine ⟨166351911750117761073619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221802549000157014764825 166351911750117761073619)
      ·
        refine ⟨249527867625176641610429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166351911750117761073619 249527867625176641610429)
        ·
          refine ⟨93572950359441240603911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249527867625176641610429 93572950359441240603911)
          ·
            refine ⟨140359425539161860905867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93572950359441240603911 140359425539161860905867)
            ·
              refine ⟨210539138308742791358801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140359425539161860905867 210539138308742791358801)
              ·
                refine ⟨157904353731557093519101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210539138308742791358801 157904353731557093519101)
                ·
                  refine ⟨59214132649333910069663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157904353731557093519101 59214132649333910069663)
                  ·
                    rfl

theorem cell20_129734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_129734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129734 prefixEnd_129734 := by exact prefixLift 129734
  have htrace : WordTrace (prefixWord ++ tailWord_129734) baseStart_129734 baseEnd_129734 := by
    simpa [prefixWord, tailWord_129734, baseEnd_129734] using wordTrace_append hprefix tailTrace_129734
  have hstable : (prefixWord ++ tailWord_129734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129734).length < 2 ^ (prefixWord ++ tailWord_129734).sum := by decide
  have hdescent : baseEnd_129734 < baseStart_129734 := by decide
  rcases family_descends (prefixWord ++ tailWord_129734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129742 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_129742 : Nat := 118140960795 + 129742 * 2 ^ 59
def prefixEnd_129742 : Nat := 4983230072969 + 3 ^ 40 * 129742 * 2
def baseEnd_129742 : Nat := 59217784067321437802963

theorem tailTrace_129742 : CollatzResearch.WordTrace tailWord_129742 prefixEnd_129742 59217784067321437802963 := by
  unfold tailWord_129742
  simp only [CollatzResearch.WordTrace]
  refine ⟨591509936996795876825935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3154719663982911343071653 591509936996795876825935)
  ·
    refine ⟨887264905495193815238903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 591509936996795876825935 887264905495193815238903)
    ·
      refine ⟨1330897358242790722858355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 887264905495193815238903 1330897358242790722858355)
      ·
        refine ⟨1996346037364186084287533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330897358242790722858355 1996346037364186084287533)
        ·
          refine ⟨748629764011569781607825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1996346037364186084287533 748629764011569781607825)
          ·
            refine ⟨561472323008677336205869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748629764011569781607825 561472323008677336205869)
            ·
              refine ⟨210552121128254001077201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 561472323008677336205869 210552121128254001077201)
              ·
                refine ⟨157914090846190500807901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210552121128254001077201 157914090846190500807901)
                ·
                  refine ⟨59217784067321437802963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157914090846190500807901 59217784067321437802963)
                  ·
                    rfl

theorem cell20_129742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_129742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129742 prefixEnd_129742 := by exact prefixLift 129742
  have htrace : WordTrace (prefixWord ++ tailWord_129742) baseStart_129742 baseEnd_129742 := by
    simpa [prefixWord, tailWord_129742, baseEnd_129742] using wordTrace_append hprefix tailTrace_129742
  have hstable : (prefixWord ++ tailWord_129742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129742).length < 2 ^ (prefixWord ++ tailWord_129742).sum := by decide
  have hdescent : baseEnd_129742 < baseStart_129742 := by decide
  rcases family_descends (prefixWord ++ tailWord_129742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129777 : List Nat := [1, 2, 2, 2, 2, 2, 3, 6]
def baseStart_129777 : Nat := 118140960795 + 129777 * 2 ^ 59
def prefixEnd_129777 : Nat := 4983230072969 + 3 ^ 40 * 129777 * 2
def baseEnd_129777 : Nat := 19744586340338957212051

theorem tailTrace_129777 : CollatzResearch.WordTrace tailWord_129777 prefixEnd_129777 19744586340338957212051 := by
  unfold tailWord_129777
  simp only [CollatzResearch.WordTrace]
  refine ⟨4733356050847567992131585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3155570700565045328087723 4733356050847567992131585)
  ·
    refine ⟨3550017038135675994098689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4733356050847567992131585 3550017038135675994098689)
    ·
      refine ⟨2662512778601756995574017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3550017038135675994098689 2662512778601756995574017)
      ·
        refine ⟨1996884583951317746680513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2662512778601756995574017 1996884583951317746680513)
        ·
          refine ⟨1497663437963488310010385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1996884583951317746680513 1497663437963488310010385)
          ·
            refine ⟨1123247578472616232507789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497663437963488310010385 1123247578472616232507789)
            ·
              refine ⟨421217841927231087190421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123247578472616232507789 421217841927231087190421)
              ·
                refine ⟨19744586340338957212051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 421217841927231087190421 19744586340338957212051)
                ·
                  rfl

theorem cell20_129777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_129777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129777 prefixEnd_129777 := by exact prefixLift 129777
  have htrace : WordTrace (prefixWord ++ tailWord_129777) baseStart_129777 baseEnd_129777 := by
    simpa [prefixWord, tailWord_129777, baseEnd_129777] using wordTrace_append hprefix tailTrace_129777
  have hstable : (prefixWord ++ tailWord_129777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129777).length < 2 ^ (prefixWord ++ tailWord_129777).sum := by decide
  have hdescent : baseEnd_129777 < baseStart_129777 := by decide
  rcases family_descends (prefixWord ++ tailWord_129777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129784 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_129784 : Nat := 118140960795 + 129784 * 2 ^ 59
def prefixEnd_129784 : Nat := 4983230072969 + 3 ^ 40 * 129784 * 2
def baseEnd_129784 : Nat := 59236954011755958402791

theorem tailTrace_129784 : CollatzResearch.WordTrace tailWord_129784 prefixEnd_129784 59236954011755958402791 := by
  unfold tailWord_129784
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366805680911104093818203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3155740907881472125090937 2366805680911104093818203)
  ·
    refine ⟨3550208521366656140727305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2366805680911104093818203 3550208521366656140727305)
    ·
      refine ⟨2662656391024992105545479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3550208521366656140727305 2662656391024992105545479)
      ·
        refine ⟨3993984586537488158318219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662656391024992105545479 3993984586537488158318219)
        ·
          refine ⟨5990976879806232237477329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3993984586537488158318219 5990976879806232237477329)
          ·
            refine ⟨4493232659854674178107997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5990976879806232237477329 4493232659854674178107997)
            ·
              refine ⟨1684962247445502816790499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4493232659854674178107997 1684962247445502816790499)
              ·
                refine ⟨2527443371168254225185749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684962247445502816790499 2527443371168254225185749)
                ·
                  refine ⟨59236954011755958402791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2527443371168254225185749 59236954011755958402791)
                  ·
                    rfl

theorem cell20_129784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_129784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129784 prefixEnd_129784 := by exact prefixLift 129784
  have htrace : WordTrace (prefixWord ++ tailWord_129784) baseStart_129784 baseEnd_129784 := by
    simpa [prefixWord, tailWord_129784, baseEnd_129784] using wordTrace_append hprefix tailTrace_129784
  have hstable : (prefixWord ++ tailWord_129784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129784).length < 2 ^ (prefixWord ++ tailWord_129784).sum := by decide
  have hdescent : baseEnd_129784 < baseStart_129784 := by decide
  rcases family_descends (prefixWord ++ tailWord_129784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129794 : List Nat := [3, 4, 1, 1, 1, 2, 8]
def baseStart_129794 : Nat := 118140960795 + 129794 * 2 ^ 59
def prefixEnd_129794 : Nat := 4983230072969 + 3 ^ 40 * 129794 * 2
def baseEnd_129794 : Nat := 6582390920471152007713

theorem tailTrace_129794 : CollatzResearch.WordTrace tailWord_129794 prefixEnd_129794 6582390920471152007713 := by
  unfold tailWord_129794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183494022946494973875109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3155984061190653263666957 1183494022946494973875109)
  ·
    refine ⟨221905129302467807601583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1183494022946494973875109 221905129302467807601583)
    ·
      refine ⟨332857693953701711402375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221905129302467807601583 332857693953701711402375)
      ·
        refine ⟨499286540930552567103563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332857693953701711402375 499286540930552567103563)
        ·
          refine ⟨748929811395828850655345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499286540930552567103563 748929811395828850655345)
          ·
            refine ⟨561697358546871637991509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748929811395828850655345 561697358546871637991509)
            ·
              refine ⟨6582390920471152007713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 561697358546871637991509 6582390920471152007713)
              ·
                rfl

theorem cell20_129794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 8].length) (baseStart_129794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129794 prefixEnd_129794 := by exact prefixLift 129794
  have htrace : WordTrace (prefixWord ++ tailWord_129794) baseStart_129794 baseEnd_129794 := by
    simpa [prefixWord, tailWord_129794, baseEnd_129794] using wordTrace_append hprefix tailTrace_129794
  have hstable : (prefixWord ++ tailWord_129794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129794).length < 2 ^ (prefixWord ++ tailWord_129794).sum := by decide
  have hdescent : baseEnd_129794 < baseStart_129794 := by decide
  rcases family_descends (prefixWord ++ tailWord_129794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129853 : List Nat := [1, 4, 1, 4, 10]
def baseStart_129853 : Nat := 118140960795 + 129853 * 2 ^ 59
def prefixEnd_129853 : Nat := 4983230072969 + 3 ^ 40 * 129853 * 2
def baseEnd_129853 : Nat := 731709228295041791389

theorem tailTrace_129853 : CollatzResearch.WordTrace tailWord_129853 prefixEnd_129853 731709228295041791389 := by
  unfold tailWord_129853
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736127998572232971898213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3157418665714821981265475 4736127998572232971898213)
  ·
    refine ⟨888023999732293682230915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4736127998572232971898213 888023999732293682230915)
    ·
      refine ⟨1332035999598440523346373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888023999732293682230915 1332035999598440523346373)
      ·
        refine ⟨249756749924707598127445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1332035999598440523346373 249756749924707598127445)
        ·
          refine ⟨731709228295041791389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 249756749924707598127445 731709228295041791389)
          ·
            rfl

theorem cell20_129853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 10].length) (baseStart_129853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129853 prefixEnd_129853 := by exact prefixLift 129853
  have htrace : WordTrace (prefixWord ++ tailWord_129853) baseStart_129853 baseEnd_129853 := by
    simpa [prefixWord, tailWord_129853, baseEnd_129853] using wordTrace_append hprefix tailTrace_129853
  have hstable : (prefixWord ++ tailWord_129853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129853).length < 2 ^ (prefixWord ++ tailWord_129853).sum := by decide
  have hdescent : baseEnd_129853 < baseStart_129853 := by decide
  rcases family_descends (prefixWord ++ tailWord_129853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129867 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_129867 : Nat := 118140960795 + 129867 * 2 ^ 59
def prefixEnd_129867 : Nat := 4983230072969 + 3 ^ 40 * 129867 * 2
def baseEnd_129867 : Nat := 59274837473376558635785

theorem tailTrace_129867 : CollatzResearch.WordTrace tailWord_129867 prefixEnd_129867 59274837473376558635785 := by
  unfold tailWord_129867
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736638620521513362907855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3157759080347675575271903 4736638620521513362907855)
  ·
    refine ⟨7104957930782270044361783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4736638620521513362907855 7104957930782270044361783)
    ·
      refine ⟨10657436896173405066542675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104957930782270044361783 10657436896173405066542675)
      ·
        refine ⟨15986155344260107599814013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10657436896173405066542675 15986155344260107599814013)
        ·
          refine ⟨5994808254097540349930255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15986155344260107599814013 5994808254097540349930255)
          ·
            refine ⟨8992212381146310524895383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994808254097540349930255 8992212381146310524895383)
            ·
              refine ⟨13488318571719465787343075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8992212381146310524895383 13488318571719465787343075)
              ·
                refine ⟨20232477857579198681014613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13488318571719465787343075 20232477857579198681014613)
                ·
                  refine ⟨59274837473376558635785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 20232477857579198681014613 59274837473376558635785)
                  ·
                    rfl

theorem cell20_129867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_129867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129867 prefixEnd_129867 := by exact prefixLift 129867
  have htrace : WordTrace (prefixWord ++ tailWord_129867) baseStart_129867 baseEnd_129867 := by
    simpa [prefixWord, tailWord_129867, baseEnd_129867] using wordTrace_append hprefix tailTrace_129867
  have hstable : (prefixWord ++ tailWord_129867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129867).length < 2 ^ (prefixWord ++ tailWord_129867).sum := by decide
  have hdescent : baseEnd_129867 < baseStart_129867 := by decide
  rcases family_descends (prefixWord ++ tailWord_129867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129877 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 3]
def baseStart_129877 : Nat := 118140960795 + 129877 * 2 ^ 59
def prefixEnd_129877 : Nat := 4983230072969 + 3 ^ 40 * 129877 * 2
def baseEnd_129877 : Nat := 59279401745860968302411

theorem tailTrace_129877 : CollatzResearch.WordTrace tailWord_129877 prefixEnd_129877 59279401745860968302411 := by
  unfold tailWord_129877
  simp only [CollatzResearch.WordTrace]
  refine ⟨4737003350485285070771885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3158002233656856713847923 4737003350485285070771885)
  ·
    refine ⟨1776376256431981901539457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4737003350485285070771885 1776376256431981901539457)
    ·
      refine ⟨1332282192323986426154593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1776376256431981901539457 1332282192323986426154593)
      ·
        refine ⟨999211644242989819615945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1332282192323986426154593 999211644242989819615945)
        ·
          refine ⟨749408733182242364711959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999211644242989819615945 749408733182242364711959)
          ·
            refine ⟨1124113099773363547067939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749408733182242364711959 1124113099773363547067939)
            ·
              refine ⟨1686169649660045320601909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124113099773363547067939 1686169649660045320601909)
              ·
                refine ⟨158078404655629248806429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1686169649660045320601909 158078404655629248806429)
                ·
                  refine ⟨59279401745860968302411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158078404655629248806429 59279401745860968302411)
                  ·
                    rfl

theorem cell20_129877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_129877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129877 prefixEnd_129877 := by exact prefixLift 129877
  have htrace : WordTrace (prefixWord ++ tailWord_129877) baseStart_129877 baseEnd_129877 := by
    simpa [prefixWord, tailWord_129877, baseEnd_129877] using wordTrace_append hprefix tailTrace_129877
  have hstable : (prefixWord ++ tailWord_129877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129877).length < 2 ^ (prefixWord ++ tailWord_129877).sum := by decide
  have hdescent : baseEnd_129877 < baseStart_129877 := by decide
  rcases family_descends (prefixWord ++ tailWord_129877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129915 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 3]
def baseStart_129915 : Nat := 118140960795 + 129915 * 2 ^ 59
def prefixEnd_129915 : Nat := 4983230072969 + 3 ^ 40 * 129915 * 2
def baseEnd_129915 : Nat := 59296745981301725035589

theorem tailTrace_129915 : CollatzResearch.WordTrace tailWord_129915 prefixEnd_129915 59296745981301725035589 := by
  unfold tailWord_129915
  simp only [CollatzResearch.WordTrace]
  refine ⟨4738389324347617560655199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3158926216231745040436799 4738389324347617560655199)
  ·
    refine ⟨7107583986521426340982799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4738389324347617560655199 7107583986521426340982799)
    ·
      refine ⟨10661375979782139511474199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7107583986521426340982799 10661375979782139511474199)
      ·
        refine ⟨15992063969673209267211299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10661375979782139511474199 15992063969673209267211299)
        ·
          refine ⟨23988095954509813900816949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15992063969673209267211299 23988095954509813900816949)
          ·
            refine ⟨2248883995735295053201589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23988095954509813900816949 2248883995735295053201589)
            ·
              refine ⟨210832874600183911237649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2248883995735295053201589 210832874600183911237649)
              ·
                refine ⟨158124655950137933428237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210832874600183911237649 158124655950137933428237)
                ·
                  refine ⟨59296745981301725035589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158124655950137933428237 59296745981301725035589)
                  ·
                    rfl

theorem cell20_129915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_129915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129915 prefixEnd_129915 := by exact prefixLift 129915
  have htrace : WordTrace (prefixWord ++ tailWord_129915) baseStart_129915 baseEnd_129915 := by
    simpa [prefixWord, tailWord_129915, baseEnd_129915] using wordTrace_append hprefix tailTrace_129915
  have hstable : (prefixWord ++ tailWord_129915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129915).length < 2 ^ (prefixWord ++ tailWord_129915).sum := by decide
  have hdescent : baseEnd_129915 < baseStart_129915 := by decide
  rcases family_descends (prefixWord ++ tailWord_129915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129942 : List Nat := [5, 3, 1, 1, 1, 2, 1, 6]
def baseStart_129942 : Nat := 118140960795 + 129942 * 2 ^ 59
def prefixEnd_129942 : Nat := 4983230072969 + 3 ^ 40 * 129942 * 2
def baseEnd_129942 : Nat := 19769689839003210378493

theorem tailTrace_129942 : CollatzResearch.WordTrace tailWord_129942 prefixEnd_129942 19769689839003210378493 := by
  unfold tailWord_129942
  simp only [CollatzResearch.WordTrace]
  refine ⟨296210880953112573243005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3159582730166534114592053 296210880953112573243005)
  ·
    refine ⟨111079080357417214966127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296210880953112573243005 111079080357417214966127)
    ·
      refine ⟨166618620536125822449191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111079080357417214966127 166618620536125822449191)
      ·
        refine ⟨249927930804188733673787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166618620536125822449191 249927930804188733673787)
        ·
          refine ⟨374891896206283100510681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249927930804188733673787 374891896206283100510681)
          ·
            refine ⟨281168922154712325383011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374891896206283100510681 281168922154712325383011)
            ·
              refine ⟨421753383232068488074517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281168922154712325383011 421753383232068488074517)
              ·
                refine ⟨19769689839003210378493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 421753383232068488074517 19769689839003210378493)
                ·
                  rfl

theorem cell20_129942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_129942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129942 prefixEnd_129942 := by exact prefixLift 129942
  have htrace : WordTrace (prefixWord ++ tailWord_129942) baseStart_129942 baseEnd_129942 := by
    simpa [prefixWord, tailWord_129942, baseEnd_129942] using wordTrace_append hprefix tailTrace_129942
  have hstable : (prefixWord ++ tailWord_129942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129942).length < 2 ^ (prefixWord ++ tailWord_129942).sum := by decide
  have hdescent : baseEnd_129942 < baseStart_129942 := by decide
  rcases family_descends (prefixWord ++ tailWord_129942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129946 : List Nat := [3, 1, 1, 4, 3, 1, 1, 6]
def baseStart_129946 : Nat := 118140960795 + 129946 * 2 ^ 59
def prefixEnd_129946 : Nat := 4983230072969 + 3 ^ 40 * 129946 * 2
def baseEnd_129946 : Nat := 19770298408667798334043

theorem tailTrace_129946 : CollatzResearch.WordTrace tailWord_129946 prefixEnd_129946 19770298408667798334043 := by
  unfold tailWord_129946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184879996808827463758423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3159679991490206570022461 1184879996808827463758423)
  ·
    refine ⟨1777319995213241195637635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1184879996808827463758423 1777319995213241195637635)
    ·
      refine ⟨2665979992819861793456453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1777319995213241195637635 2665979992819861793456453)
      ·
        refine ⟨499871248653724086273085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2665979992819861793456453 499871248653724086273085)
        ·
          refine ⟨187451718245146532352407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499871248653724086273085 187451718245146532352407)
          ·
            refine ⟨281177577367719798528611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187451718245146532352407 281177577367719798528611)
            ·
              refine ⟨421766366051579697792917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281177577367719798528611 421766366051579697792917)
              ·
                refine ⟨19770298408667798334043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 421766366051579697792917 19770298408667798334043)
                ·
                  rfl

theorem cell20_129946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_129946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129946 prefixEnd_129946 := by exact prefixLift 129946
  have htrace : WordTrace (prefixWord ++ tailWord_129946) baseStart_129946 baseEnd_129946 := by
    simpa [prefixWord, tailWord_129946, baseEnd_129946] using wordTrace_append hprefix tailTrace_129946
  have hstable : (prefixWord ++ tailWord_129946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129946).length < 2 ^ (prefixWord ++ tailWord_129946).sum := by decide
  have hdescent : baseEnd_129946 < baseStart_129946 := by decide
  rcases family_descends (prefixWord ++ tailWord_129946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129953 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_129953 : Nat := 118140960795 + 129953 * 2 ^ 59
def prefixEnd_129953 : Nat := 4983230072969 + 3 ^ 40 * 129953 * 2
def baseEnd_129953 : Nat := 59314090216742481768767

theorem tailTrace_129953 : CollatzResearch.WordTrace tailWord_129953 prefixEnd_129953 59314090216742481768767 := by
  unfold tailWord_129953
  simp only [CollatzResearch.WordTrace]
  refine ⟨4739775298209950050538513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3159850198806633367025675 4739775298209950050538513)
  ·
    refine ⟨3554831473657462537903885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4739775298209950050538513 3554831473657462537903885)
    ·
      refine ⟨1333061802621548451713957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3554831473657462537903885 1333061802621548451713957)
      ·
        refine ⟨249949087991540334696367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1333061802621548451713957 249949087991540334696367)
        ·
          refine ⟨374923631987310502044551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249949087991540334696367 374923631987310502044551)
          ·
            refine ⟨562385447980965753066827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374923631987310502044551 562385447980965753066827)
            ·
              refine ⟨843578171971448629600241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562385447980965753066827 843578171971448629600241)
              ·
                refine ⟨632683628978586472200181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843578171971448629600241 632683628978586472200181)
                ·
                  refine ⟨59314090216742481768767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 632683628978586472200181 59314090216742481768767)
                  ·
                    rfl

theorem cell20_129953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_129953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129953 prefixEnd_129953 := by exact prefixLift 129953
  have htrace : WordTrace (prefixWord ++ tailWord_129953) baseStart_129953 baseEnd_129953 := by
    simpa [prefixWord, tailWord_129953, baseEnd_129953] using wordTrace_append hprefix tailTrace_129953
  have hstable : (prefixWord ++ tailWord_129953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129953).length < 2 ^ (prefixWord ++ tailWord_129953).sum := by decide
  have hdescent : baseEnd_129953 < baseStart_129953 := by decide
  rcases family_descends (prefixWord ++ tailWord_129953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129977 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 4]
def baseStart_129977 : Nat := 118140960795 + 129977 * 2 ^ 59
def prefixEnd_129977 : Nat := 4983230072969 + 3 ^ 40 * 129977 * 2
def baseEnd_129977 : Nat := 59325044470705064968669

theorem tailTrace_129977 : CollatzResearch.WordTrace tailWord_129977 prefixEnd_129977 59325044470705064968669 := by
  unfold tailWord_129977
  simp only [CollatzResearch.WordTrace]
  refine ⟨4740650650123002149412185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3160433766748668099608123 4740650650123002149412185)
  ·
    refine ⟨3555487987592251612059139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4740650650123002149412185 3555487987592251612059139)
    ·
      refine ⟨5333231981388377418088709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555487987592251612059139 5333231981388377418088709)
      ·
        refine ⟨999980996510320765891633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5333231981388377418088709 999980996510320765891633)
        ·
          refine ⟨749985747382740574418725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999980996510320765891633 749985747382740574418725)
          ·
            refine ⟨140622327634263857703511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 749985747382740574418725 140622327634263857703511)
            ·
              refine ⟨210933491451395786555267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140622327634263857703511 210933491451395786555267)
              ·
                refine ⟨316400237177093679832901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210933491451395786555267 316400237177093679832901)
                ·
                  refine ⟨59325044470705064968669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316400237177093679832901 59325044470705064968669)
                  ·
                    rfl

theorem cell20_129977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_129977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_129977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_129977 prefixEnd_129977 := by exact prefixLift 129977
  have htrace : WordTrace (prefixWord ++ tailWord_129977) baseStart_129977 baseEnd_129977 := by
    simpa [prefixWord, tailWord_129977, baseEnd_129977] using wordTrace_append hprefix tailTrace_129977
  have hstable : (prefixWord ++ tailWord_129977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129977).length < 2 ^ (prefixWord ++ tailWord_129977).sum := by decide
  have hdescent : baseEnd_129977 < baseStart_129977 := by decide
  rcases family_descends (prefixWord ++ tailWord_129977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130060 : List Nat := [2, 2, 1, 2, 3, 3, 3, 4]
def baseStart_130060 : Nat := 118140960795 + 130060 * 2 ^ 59
def prefixEnd_130060 : Nat := 4983230072969 + 3 ^ 40 * 130060 * 2
def baseEnd_130060 : Nat := 19787642644108555067221

theorem tailTrace_130060 : CollatzResearch.WordTrace tailWord_130060 prefixEnd_130060 19787642644108555067221 := by
  unfold tailWord_130060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2371838954411153662341817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3162451939214871549789089 2371838954411153662341817)
  ·
    refine ⟨1778879215808365246756363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2371838954411153662341817 1778879215808365246756363)
    ·
      refine ⟨2668318823712547870134545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1778879215808365246756363 2668318823712547870134545)
      ·
        refine ⟨2001239117784410902600909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2668318823712547870134545 2001239117784410902600909)
        ·
          refine ⟨750464669169154088475341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2001239117784410902600909 750464669169154088475341)
          ·
            refine ⟨281424250938432783178253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 750464669169154088475341 281424250938432783178253)
            ·
              refine ⟨105534094101912293691845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281424250938432783178253 105534094101912293691845)
              ·
                refine ⟨19787642644108555067221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105534094101912293691845 19787642644108555067221)
                ·
                  rfl

theorem cell20_130060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_130060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130060 prefixEnd_130060 := by exact prefixLift 130060
  have htrace : WordTrace (prefixWord ++ tailWord_130060) baseStart_130060 baseEnd_130060 := by
    simpa [prefixWord, tailWord_130060, baseEnd_130060] using wordTrace_append hprefix tailTrace_130060
  have hstable : (prefixWord ++ tailWord_130060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130060).length < 2 ^ (prefixWord ++ tailWord_130060).sum := by decide
  have hdescent : baseEnd_130060 < baseStart_130060 := by decide
  rcases family_descends (prefixWord ++ tailWord_130060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130080 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 3]
def baseStart_130080 : Nat := 118140960795 + 130080 * 2 ^ 59
def prefixEnd_130080 : Nat := 4983230072969 + 3 ^ 40 * 130080 * 2
def baseEnd_130080 : Nat := 59372056477294484534915

theorem tailTrace_130080 : CollatzResearch.WordTrace tailWord_130080 prefixEnd_130080 59372056477294484534915 := by
  unfold tailWord_130080
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372203684374925370205847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3162938245833233826941129 2372203684374925370205847)
  ·
    refine ⟨3558305526562388055308771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2372203684374925370205847 3558305526562388055308771)
    ·
      refine ⟨5337458289843582082963157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3558305526562388055308771 5337458289843582082963157)
      ·
        refine ⟨125096678668208955069449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5337458289843582082963157 125096678668208955069449)
        ·
          refine ⟨93822509001156716302087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125096678668208955069449 93822509001156716302087)
          ·
            refine ⟨140733763501735074453131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93822509001156716302087 140733763501735074453131)
            ·
              refine ⟨211100645252602611679697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140733763501735074453131 211100645252602611679697)
              ·
                refine ⟨158325483939451958759773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211100645252602611679697 158325483939451958759773)
                ·
                  refine ⟨59372056477294484534915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158325483939451958759773 59372056477294484534915)
                  ·
                    rfl

theorem cell20_130080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_130080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130080 prefixEnd_130080 := by exact prefixLift 130080
  have htrace : WordTrace (prefixWord ++ tailWord_130080) baseStart_130080 baseEnd_130080 := by
    simpa [prefixWord, tailWord_130080, baseEnd_130080] using wordTrace_append hprefix tailTrace_130080
  have hstable : (prefixWord ++ tailWord_130080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130080).length < 2 ^ (prefixWord ++ tailWord_130080).sum := by decide
  have hdescent : baseEnd_130080 < baseStart_130080 := by decide
  rcases family_descends (prefixWord ++ tailWord_130080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130081 : List Nat := [1, 2, 3, 2, 3, 2, 7]
def baseStart_130081 : Nat := 118140960795 + 130081 * 2 ^ 59
def prefixEnd_130081 : Nat := 4983230072969 + 3 ^ 40 * 130081 * 2
def baseEnd_130081 : Nat := 6596945878282547277953

theorem tailTrace_130081 : CollatzResearch.WordTrace tailWord_130081 prefixEnd_130081 6596945878282547277953 := by
  unfold tailWord_130081
  simp only [CollatzResearch.WordTrace]
  refine ⟨4744443841746227911198097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3162962561164151940798731 4744443841746227911198097)
  ·
    refine ⟨3558332881309670933398573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4744443841746227911198097 3558332881309670933398573)
    ·
      refine ⟨1334374830491126600024465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3558332881309670933398573 1334374830491126600024465)
      ·
        refine ⟨1000781122868344950018349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1334374830491126600024465 1000781122868344950018349)
        ·
          refine ⟨375292921075629356256881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1000781122868344950018349 375292921075629356256881)
          ·
            refine ⟨281469690806722017192661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375292921075629356256881 281469690806722017192661)
            ·
              refine ⟨6596945878282547277953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 281469690806722017192661 6596945878282547277953)
              ·
                rfl

theorem cell20_130081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 7].length) (baseStart_130081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130081 prefixEnd_130081 := by exact prefixLift 130081
  have htrace : WordTrace (prefixWord ++ tailWord_130081) baseStart_130081 baseEnd_130081 := by
    simpa [prefixWord, tailWord_130081, baseEnd_130081] using wordTrace_append hprefix tailTrace_130081
  have hstable : (prefixWord ++ tailWord_130081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130081).length < 2 ^ (prefixWord ++ tailWord_130081).sum := by decide
  have hdescent : baseEnd_130081 < baseStart_130081 := by decide
  rcases family_descends (prefixWord ++ tailWord_130081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130084 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_130084 : Nat := 118140960795 + 130084 * 2 ^ 59
def prefixEnd_130084 : Nat := 4983230072969 + 3 ^ 40 * 130084 * 2
def baseEnd_130084 : Nat := 59373882186288248401565

theorem tailTrace_130084 : CollatzResearch.WordTrace tailWord_130084 prefixEnd_130084 59373882186288248401565 := by
  unfold tailWord_130084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372276630367679711778653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3163035507156906282371537 2372276630367679711778653)
  ·
    refine ⟨889603736387879891916995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2372276630367679711778653 889603736387879891916995)
    ·
      refine ⟨1334405604581819837875493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 889603736387879891916995 1334405604581819837875493)
      ·
        refine ⟨250201050859091219601655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1334405604581819837875493 250201050859091219601655)
        ·
          refine ⟨375301576288636829402483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250201050859091219601655 375301576288636829402483)
          ·
            refine ⟨562952364432955244103725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375301576288636829402483 562952364432955244103725)
            ·
              refine ⟨211107136662358216538897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562952364432955244103725 211107136662358216538897)
              ·
                refine ⟨158330352496768662404173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211107136662358216538897 158330352496768662404173)
                ·
                  refine ⟨59373882186288248401565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158330352496768662404173 59373882186288248401565)
                  ·
                    rfl

theorem cell20_130084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_130084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130084 prefixEnd_130084 := by exact prefixLift 130084
  have htrace : WordTrace (prefixWord ++ tailWord_130084) baseStart_130084 baseEnd_130084 := by
    simpa [prefixWord, tailWord_130084, baseEnd_130084] using wordTrace_append hprefix tailTrace_130084
  have hstable : (prefixWord ++ tailWord_130084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130084).length < 2 ^ (prefixWord ++ tailWord_130084).sum := by decide
  have hdescent : baseEnd_130084 < baseStart_130084 := by decide
  rcases family_descends (prefixWord ++ tailWord_130084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130119 : List Nat := [1, 1, 4, 1, 3, 3, 1, 6]
def baseStart_130119 : Nat := 118140960795 + 130119 * 2 ^ 59
def prefixEnd_130119 : Nat := 4983230072969 + 3 ^ 40 * 130119 * 2
def baseEnd_130119 : Nat := 19796619046661227411585

theorem tailTrace_130119 : CollatzResearch.WordTrace tailWord_130119 prefixEnd_130119 19796619046661227411585 := by
  unfold tailWord_130119
  simp only [CollatzResearch.WordTrace]
  refine ⟨4745829815608560401081411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3163886543739040267387607 4745829815608560401081411)
  ·
    refine ⟨7118744723412840601622117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4745829815608560401081411 7118744723412840601622117)
    ·
      refine ⟨1334764635639907612804147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7118744723412840601622117 1334764635639907612804147)
      ·
        refine ⟨2002146953459861419206221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334764635639907612804147 2002146953459861419206221)
        ·
          refine ⟨750805107547448032202333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2002146953459861419206221 750805107547448032202333)
          ·
            refine ⟨281551915330293012075875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 750805107547448032202333 281551915330293012075875)
            ·
              refine ⟨422327872995439518113813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281551915330293012075875 422327872995439518113813)
              ·
                refine ⟨19796619046661227411585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 422327872995439518113813 19796619046661227411585)
                ·
                  rfl

theorem cell20_130119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 6].length) (baseStart_130119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130119 prefixEnd_130119 := by exact prefixLift 130119
  have htrace : WordTrace (prefixWord ++ tailWord_130119) baseStart_130119 baseEnd_130119 := by
    simpa [prefixWord, tailWord_130119, baseEnd_130119] using wordTrace_append hprefix tailTrace_130119
  have hstable : (prefixWord ++ tailWord_130119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130119).length < 2 ^ (prefixWord ++ tailWord_130119).sum := by decide
  have hdescent : baseEnd_130119 < baseStart_130119 := by decide
  rcases family_descends (prefixWord ++ tailWord_130119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130125 : List Nat := [1, 6, 1, 1, 1, 4, 1, 3, 2]
def baseStart_130125 : Nat := 118140960795 + 130125 * 2 ^ 59
def prefixEnd_130125 : Nat := 4983230072969 + 3 ^ 40 * 130125 * 2
def baseEnd_130125 : Nat := 59392595703474328034731

theorem tailTrace_130125 : CollatzResearch.WordTrace tailWord_130125 prefixEnd_130125 59392595703474328034731 := by
  unfold tailWord_130125
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746048653586823425799829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3164032435724548950533219 4746048653586823425799829)
  ·
    refine ⟨222471030636882348084367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4746048653586823425799829 222471030636882348084367)
    ·
      refine ⟨333706545955323522126551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222471030636882348084367 333706545955323522126551)
      ·
        refine ⟨500559818932985283189827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333706545955323522126551 500559818932985283189827)
        ·
          refine ⟨750839728399477924784741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500559818932985283189827 750839728399477924784741)
          ·
            refine ⟨140782449074902110897139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 750839728399477924784741 140782449074902110897139)
            ·
              refine ⟨211173673612353166345709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140782449074902110897139 211173673612353166345709)
              ·
                refine ⟨79190127604632437379641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211173673612353166345709 79190127604632437379641)
                ·
                  refine ⟨59392595703474328034731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79190127604632437379641 59392595703474328034731)
                  ·
                    rfl

theorem cell20_130125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_130125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130125 prefixEnd_130125 := by exact prefixLift 130125
  have htrace : WordTrace (prefixWord ++ tailWord_130125) baseStart_130125 baseEnd_130125 := by
    simpa [prefixWord, tailWord_130125, baseEnd_130125] using wordTrace_append hprefix tailTrace_130125
  have hstable : (prefixWord ++ tailWord_130125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130125).length < 2 ^ (prefixWord ++ tailWord_130125).sum := by decide
  have hdescent : baseEnd_130125 < baseStart_130125 := by decide
  rcases family_descends (prefixWord ++ tailWord_130125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130126 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_130126 : Nat := 118140960795 + 130126 * 2 ^ 59
def prefixEnd_130126 : Nat := 4983230072969 + 3 ^ 40 * 130126 * 2
def baseEnd_130126 : Nat := 59393052130722769001393

theorem tailTrace_130126 : CollatzResearch.WordTrace tailWord_130126 prefixEnd_130126 59393052130722769001393 := by
  unfold tailWord_130126
  simp only [CollatzResearch.WordTrace]
  refine ⟨593260640822900074573279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3164056751055467064390821 593260640822900074573279)
  ·
    refine ⟨889890961234350111859919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 593260640822900074573279 889890961234350111859919)
    ·
      refine ⟨1334836441851525167789879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 889890961234350111859919 1334836441851525167789879)
      ·
        refine ⟨2002254662777287751684819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334836441851525167789879 2002254662777287751684819)
        ·
          refine ⟨3003381994165931627527229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002254662777287751684819 3003381994165931627527229)
          ·
            refine ⟨1126268247812224360322711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3003381994165931627527229 1126268247812224360322711)
            ·
              refine ⟨1689402371718336540484067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126268247812224360322711 1689402371718336540484067)
              ·
                refine ⟨2534103557577504810726101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689402371718336540484067 2534103557577504810726101)
                ·
                  refine ⟨59393052130722769001393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2534103557577504810726101 59393052130722769001393)
                  ·
                    rfl

theorem cell20_130126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_130126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130126 prefixEnd_130126 := by exact prefixLift 130126
  have htrace : WordTrace (prefixWord ++ tailWord_130126) baseStart_130126 baseEnd_130126 := by
    simpa [prefixWord, tailWord_130126, baseEnd_130126] using wordTrace_append hprefix tailTrace_130126
  have hstable : (prefixWord ++ tailWord_130126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130126).length < 2 ^ (prefixWord ++ tailWord_130126).sum := by decide
  have hdescent : baseEnd_130126 < baseStart_130126 := by decide
  rcases family_descends (prefixWord ++ tailWord_130126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130129 : List Nat := [1, 2, 2, 1, 3, 1, 5, 3, 2]
def baseStart_130129 : Nat := 118140960795 + 130129 * 2 ^ 59
def prefixEnd_130129 : Nat := 4983230072969 + 3 ^ 40 * 130129 * 2
def baseEnd_130129 : Nat := 59394421412468091901381

theorem tailTrace_130129 : CollatzResearch.WordTrace tailWord_130129 prefixEnd_130129 59394421412468091901381 := by
  unfold tailWord_130129
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746194545572332108945441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3164129697048221405963627 4746194545572332108945441)
  ·
    refine ⟨3559645909179249081709081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4746194545572332108945441 3559645909179249081709081)
    ·
      refine ⟨2669734431884436811281811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3559645909179249081709081 2669734431884436811281811)
      ·
        refine ⟨4004601647826655216922717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669734431884436811281811 4004601647826655216922717)
        ·
          refine ⟨1501725617934995706346019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4004601647826655216922717 1501725617934995706346019)
          ·
            refine ⟨2252588426902493559519029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501725617934995706346019 2252588426902493559519029)
            ·
              refine ⟨211180165022108771204909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2252588426902493559519029 211180165022108771204909)
              ·
                refine ⟨79192561883290789201841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211180165022108771204909 79192561883290789201841)
                ·
                  refine ⟨59394421412468091901381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79192561883290789201841 59394421412468091901381)
                  ·
                    rfl

theorem cell20_130129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_130129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130129 prefixEnd_130129 := by exact prefixLift 130129
  have htrace : WordTrace (prefixWord ++ tailWord_130129) baseStart_130129 baseEnd_130129 := by
    simpa [prefixWord, tailWord_130129, baseEnd_130129] using wordTrace_append hprefix tailTrace_130129
  have hstable : (prefixWord ++ tailWord_130129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130129).length < 2 ^ (prefixWord ++ tailWord_130129).sum := by decide
  have hdescent : baseEnd_130129 < baseStart_130129 := by decide
  rcases family_descends (prefixWord ++ tailWord_130129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130146 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_130146 : Nat := 118140960795 + 130146 * 2 ^ 59
def prefixEnd_130146 : Nat := 4983230072969 + 3 ^ 40 * 130146 * 2
def baseEnd_130146 : Nat := 59402180675691588334645

theorem tailTrace_130146 : CollatzResearch.WordTrace tailWord_130146 prefixEnd_130146 59402180675691588334645 := by
  unfold tailWord_130146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1186703646627686003078573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3164543057673829341542861 1186703646627686003078573)
  ·
    refine ⟨445013867485382251154465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1186703646627686003078573 445013867485382251154465)
    ·
      refine ⟨333760400614036688365849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445013867485382251154465 333760400614036688365849)
      ·
        refine ⟨250320300460527516274387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333760400614036688365849 250320300460527516274387)
        ·
          refine ⟨375480450690791274411581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250320300460527516274387 375480450690791274411581)
          ·
            refine ⟨140805169009046727904343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375480450690791274411581 140805169009046727904343)
            ·
              refine ⟨211207753513570091856515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140805169009046727904343 211207753513570091856515)
              ·
                refine ⟨316811630270355137784773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211207753513570091856515 316811630270355137784773)
                ·
                  refine ⟨59402180675691588334645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316811630270355137784773 59402180675691588334645)
                  ·
                    rfl

theorem cell20_130146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_130146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130146 prefixEnd_130146 := by exact prefixLift 130146
  have htrace : WordTrace (prefixWord ++ tailWord_130146) baseStart_130146 baseEnd_130146 := by
    simpa [prefixWord, tailWord_130146, baseEnd_130146] using wordTrace_append hprefix tailTrace_130146
  have hstable : (prefixWord ++ tailWord_130146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130146).length < 2 ^ (prefixWord ++ tailWord_130146).sum := by decide
  have hdescent : baseEnd_130146 < baseStart_130146 := by decide
  rcases family_descends (prefixWord ++ tailWord_130146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130157 : List Nat := [1, 5, 1, 1, 2, 2, 1, 7]
def baseStart_130157 : Nat := 118140960795 + 130157 * 2 ^ 59
def prefixEnd_130157 : Nat := 4983230072969 + 3 ^ 40 * 130157 * 2
def baseEnd_130157 : Nat := 19802400458474812989311

theorem tailTrace_130157 : CollatzResearch.WordTrace tailWord_130157 prefixEnd_130157 19802400458474812989311 := by
  unfold tailWord_130157
  simp only [CollatzResearch.WordTrace]
  refine ⟨4747215789470892890964725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3164810526313928593976483 4747215789470892890964725)
  ·
    refine ⟨445051480262896208527943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4747215789470892890964725 445051480262896208527943)
    ·
      refine ⟨667577220394344312791915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445051480262896208527943 667577220394344312791915)
      ·
        refine ⟨1001365830591516469187873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667577220394344312791915 1001365830591516469187873)
        ·
          refine ⟨751024372943637351890905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1001365830591516469187873 751024372943637351890905)
          ·
            refine ⟨563268279707728013918179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751024372943637351890905 563268279707728013918179)
            ·
              refine ⟨844902419561592020877269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563268279707728013918179 844902419561592020877269)
              ·
                refine ⟨19802400458474812989311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 844902419561592020877269 19802400458474812989311)
                ·
                  rfl

theorem cell20_130157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_130157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130157 prefixEnd_130157 := by exact prefixLift 130157
  have htrace : WordTrace (prefixWord ++ tailWord_130157) baseStart_130157 baseEnd_130157 := by
    simpa [prefixWord, tailWord_130157, baseEnd_130157] using wordTrace_append hprefix tailTrace_130157
  have hstable : (prefixWord ++ tailWord_130157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130157).length < 2 ^ (prefixWord ++ tailWord_130157).sum := by decide
  have hdescent : baseEnd_130157 < baseStart_130157 := by decide
  rcases family_descends (prefixWord ++ tailWord_130157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130171 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_130171 : Nat := 118140960795 + 130171 * 2 ^ 59
def prefixEnd_130171 : Nat := 4983230072969 + 3 ^ 40 * 130171 * 2
def baseEnd_130171 : Nat := 59413591356902612501209

theorem tailTrace_130171 : CollatzResearch.WordTrace tailWord_130171 prefixEnd_130171 59413591356902612501209 := by
  unfold tailWord_130171
  simp only [CollatzResearch.WordTrace]
  refine ⟨4747726411420173281974367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3165150940946782187982911 4747726411420173281974367)
  ·
    refine ⟨7121589617130259922961551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4747726411420173281974367 7121589617130259922961551)
    ·
      refine ⟨10682384425695389884442327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7121589617130259922961551 10682384425695389884442327)
      ·
        refine ⟨16023576638543084826663491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10682384425695389884442327 16023576638543084826663491)
        ·
          refine ⟨24035364957814627239995237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16023576638543084826663491 24035364957814627239995237)
          ·
            refine ⟨4506630929590242607499107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24035364957814627239995237 4506630929590242607499107)
            ·
              refine ⟨6759946394385363911248661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506630929590242607499107 6759946394385363911248661)
              ·
                refine ⟨316872487236813933339781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6759946394385363911248661 316872487236813933339781)
                ·
                  refine ⟨59413591356902612501209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 316872487236813933339781 59413591356902612501209)
                  ·
                    rfl

theorem cell20_130171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_130171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130171 prefixEnd_130171 := by exact prefixLift 130171
  have htrace : WordTrace (prefixWord ++ tailWord_130171) baseStart_130171 baseEnd_130171 := by
    simpa [prefixWord, tailWord_130171, baseEnd_130171] using wordTrace_append hprefix tailTrace_130171
  have hstable : (prefixWord ++ tailWord_130171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130171).length < 2 ^ (prefixWord ++ tailWord_130171).sum := by decide
  have hdescent : baseEnd_130171 < baseStart_130171 := by decide
  rcases family_descends (prefixWord ++ tailWord_130171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130205 : List Nat := [1, 4, 2, 1, 1, 2, 3, 4, 2]
def baseStart_130205 : Nat := 118140960795 + 130205 * 2 ^ 59
def prefixEnd_130205 : Nat := 4983230072969 + 3 ^ 40 * 130205 * 2
def baseEnd_130205 : Nat := 59429109883349605367737

theorem tailTrace_130205 : CollatzResearch.WordTrace tailWord_130205 prefixEnd_130205 59429109883349605367737 := by
  unfold tailWord_130205
  simp only [CollatzResearch.WordTrace]
  refine ⟨4748966493296997088712069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3165977662197998059141379 4748966493296997088712069)
  ·
    refine ⟨890431217493186954133513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4748966493296997088712069 890431217493186954133513)
    ·
      refine ⟨667823413119890215600135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 890431217493186954133513 667823413119890215600135)
      ·
        refine ⟨1001735119679835323400203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 667823413119890215600135 1001735119679835323400203)
        ·
          refine ⟨1502602679519752985100305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001735119679835323400203 1502602679519752985100305)
          ·
            refine ⟨1126952009639814738825229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502602679519752985100305 1126952009639814738825229)
            ·
              refine ⟨422607003614930527059461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126952009639814738825229 422607003614930527059461)
              ·
                refine ⟨79238813177799473823649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422607003614930527059461 79238813177799473823649)
                ·
                  refine ⟨59429109883349605367737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79238813177799473823649 59429109883349605367737)
                  ·
                    rfl

theorem cell20_130205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_130205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130205 prefixEnd_130205 := by exact prefixLift 130205
  have htrace : WordTrace (prefixWord ++ tailWord_130205) baseStart_130205 baseEnd_130205 := by
    simpa [prefixWord, tailWord_130205, baseEnd_130205] using wordTrace_append hprefix tailTrace_130205
  have hstable : (prefixWord ++ tailWord_130205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130205).length < 2 ^ (prefixWord ++ tailWord_130205).sum := by decide
  have hdescent : baseEnd_130205 < baseStart_130205 := by decide
  rcases family_descends (prefixWord ++ tailWord_130205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130212 : List Nat := [2, 3, 1, 2, 3, 3, 1, 5]
def baseStart_130212 : Nat := 118140960795 + 130212 * 2 ^ 59
def prefixEnd_130212 : Nat := 4983230072969 + 3 ^ 40 * 130212 * 2
def baseEnd_130212 : Nat := 19810768291362897378125

theorem tailTrace_130212 : CollatzResearch.WordTrace tailWord_130212 prefixEnd_130212 19810768291362897378125 := by
  unfold tailWord_130212
  simp only [CollatzResearch.WordTrace]
  refine ⟨2374610902135818642108445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3166147869514424856144593 2374610902135818642108445)
  ·
    refine ⟨890479088300931990790667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2374610902135818642108445 890479088300931990790667)
    ·
      refine ⟨1335718632451397986186001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890479088300931990790667 1335718632451397986186001)
      ·
        refine ⟨1001788974338548489639501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1335718632451397986186001 1001788974338548489639501)
        ·
          refine ⟨375670865376955683614813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1001788974338548489639501 375670865376955683614813)
          ·
            refine ⟨140876574516358381355555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375670865376955683614813 140876574516358381355555)
            ·
              refine ⟨211314861774537572033333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140876574516358381355555 211314861774537572033333)
              ·
                refine ⟨19810768291362897378125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211314861774537572033333 19810768291362897378125)
                ·
                  rfl

theorem cell20_130212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_130212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130212 prefixEnd_130212 := by exact prefixLift 130212
  have htrace : WordTrace (prefixWord ++ tailWord_130212) baseStart_130212 baseEnd_130212 := by
    simpa [prefixWord, tailWord_130212, baseEnd_130212] using wordTrace_append hprefix tailTrace_130212
  have hstable : (prefixWord ++ tailWord_130212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130212).length < 2 ^ (prefixWord ++ tailWord_130212).sum := by decide
  have hdescent : baseEnd_130212 < baseStart_130212 := by decide
  rcases family_descends (prefixWord ++ tailWord_130212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130226 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_130226 : Nat := 118140960795 + 130226 * 2 ^ 59
def prefixEnd_130226 : Nat := 4983230072969 + 3 ^ 40 * 130226 * 2
def baseEnd_130226 : Nat := 59438694855566865667651

theorem tailTrace_130226 : CollatzResearch.WordTrace tailWord_130226 prefixEnd_130226 59438694855566865667651 := by
  unfold tailWord_130226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187433106555229418806633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3166488284147278450151021 1187433106555229418806633)
  ·
    refine ⟨890574829916422064104975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1187433106555229418806633 890574829916422064104975)
    ·
      refine ⟨1335862244874633096157463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890574829916422064104975 1335862244874633096157463)
      ·
        refine ⟨2003793367311949644236195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335862244874633096157463 2003793367311949644236195)
        ·
          refine ⟨3005690050967924466354293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003793367311949644236195 3005690050967924466354293)
          ·
            refine ⟨281783442278242918720715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3005690050967924466354293 281783442278242918720715)
            ·
              refine ⟨422675163417364378081073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281783442278242918720715 422675163417364378081073)
              ·
                refine ⟨317006372563023283560805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422675163417364378081073 317006372563023283560805)
                ·
                  refine ⟨59438694855566865667651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317006372563023283560805 59438694855566865667651)
                  ·
                    rfl

theorem cell20_130226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_130226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130226 prefixEnd_130226 := by exact prefixLift 130226
  have htrace : WordTrace (prefixWord ++ tailWord_130226) baseStart_130226 baseEnd_130226 := by
    simpa [prefixWord, tailWord_130226, baseEnd_130226] using wordTrace_append hprefix tailTrace_130226
  have hstable : (prefixWord ++ tailWord_130226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130226).length < 2 ^ (prefixWord ++ tailWord_130226).sum := by decide
  have hdescent : baseEnd_130226 < baseStart_130226 := by decide
  rcases family_descends (prefixWord ++ tailWord_130226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130246 : List Nat := [6, 1, 2, 2, 1, 1, 7]
def baseStart_130246 : Nat := 118140960795 + 130246 * 2 ^ 59
def prefixEnd_130246 : Nat := 4983230072969 + 3 ^ 40 * 130246 * 2
def baseEnd_130246 : Nat := 6605313711170631666767

theorem tailTrace_130246 : CollatzResearch.WordTrace tailWord_130246 prefixEnd_130246 6605313711170631666767 := by
  unfold tailWord_130246
  simp only [CollatzResearch.WordTrace]
  refine ⟨148451933942139409092331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3166974590765640727303061 148451933942139409092331)
  ·
    refine ⟨222677900913209113638497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148451933942139409092331 222677900913209113638497)
    ·
      refine ⟨167008425684906835228873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222677900913209113638497 167008425684906835228873)
      ·
        refine ⟨125256319263680126421655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167008425684906835228873 125256319263680126421655)
        ·
          refine ⟨187884478895520189632483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125256319263680126421655 187884478895520189632483)
          ·
            refine ⟨281826718343280284448725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187884478895520189632483 281826718343280284448725)
            ·
              refine ⟨6605313711170631666767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 281826718343280284448725 6605313711170631666767)
              ·
                rfl

theorem cell20_130246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 7].length) (baseStart_130246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130246 prefixEnd_130246 := by exact prefixLift 130246
  have htrace : WordTrace (prefixWord ++ tailWord_130246) baseStart_130246 baseEnd_130246 := by
    simpa [prefixWord, tailWord_130246, baseEnd_130246] using wordTrace_append hprefix tailTrace_130246
  have hstable : (prefixWord ++ tailWord_130246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130246).length < 2 ^ (prefixWord ++ tailWord_130246).sum := by decide
  have hdescent : baseEnd_130246 < baseStart_130246 := by decide
  rcases family_descends (prefixWord ++ tailWord_130246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130253 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 5]
def baseStart_130253 : Nat := 118140960795 + 130253 * 2 ^ 59
def prefixEnd_130253 : Nat := 4983230072969 + 3 ^ 40 * 130253 * 2
def baseEnd_130253 : Nat := 59451018391274771767541

theorem tailTrace_130253 : CollatzResearch.WordTrace tailWord_130253 prefixEnd_130253 59451018391274771767541 := by
  unfold tailWord_130253
  simp only [CollatzResearch.WordTrace]
  refine ⟨4750717197123101286459413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3167144798082067524306275 4750717197123101286459413)
  ·
    refine ⟨222689868615145372802785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4750717197123101286459413 222689868615145372802785)
    ·
      refine ⟨167017401461359029602089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222689868615145372802785 167017401461359029602089)
      ·
        refine ⟨125263051096019272201567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167017401461359029602089 125263051096019272201567)
        ·
          refine ⟨187894576644028908302351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125263051096019272201567 187894576644028908302351)
          ·
            refine ⟨281841864966043362453527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187894576644028908302351 281841864966043362453527)
            ·
              refine ⟨422762797449065043680291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281841864966043362453527 422762797449065043680291)
              ·
                refine ⟨634144196173597565520437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422762797449065043680291 634144196173597565520437)
                ·
                  refine ⟨59451018391274771767541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 634144196173597565520437 59451018391274771767541)
                  ·
                    rfl

theorem cell20_130253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_130253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130253 prefixEnd_130253 := by exact prefixLift 130253
  have htrace : WordTrace (prefixWord ++ tailWord_130253) baseStart_130253 baseEnd_130253 := by
    simpa [prefixWord, tailWord_130253, baseEnd_130253] using wordTrace_append hprefix tailTrace_130253
  have hstable : (prefixWord ++ tailWord_130253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130253).length < 2 ^ (prefixWord ++ tailWord_130253).sum := by decide
  have hdescent : baseEnd_130253 < baseStart_130253 := by decide
  rcases family_descends (prefixWord ++ tailWord_130253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130260 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 4]
def baseStart_130260 : Nat := 118140960795 + 130260 * 2 ^ 59
def prefixEnd_130260 : Nat := 4983230072969 + 3 ^ 40 * 130260 * 2
def baseEnd_130260 : Nat := 59454213382013858534179

theorem tailTrace_130260 : CollatzResearch.WordTrace tailWord_130260 prefixEnd_130260 59454213382013858534179 := by
  unfold tailWord_130260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2375486254048870740982117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3167315005398494321309489 2375486254048870740982117)
  ·
    refine ⟨445403672634163263934147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2375486254048870740982117 445403672634163263934147)
    ·
      refine ⟨668105508951244895901221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445403672634163263934147 668105508951244895901221)
      ·
        refine ⟨125269782928358417981479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 668105508951244895901221 125269782928358417981479)
        ·
          refine ⟨187904674392537626972219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125269782928358417981479 187904674392537626972219)
          ·
            refine ⟨281857011588806440458329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187904674392537626972219 281857011588806440458329)
            ·
              refine ⟨211392758691604830343747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281857011588806440458329 211392758691604830343747)
              ·
                refine ⟨317089138037407245515621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211392758691604830343747 317089138037407245515621)
                ·
                  refine ⟨59454213382013858534179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317089138037407245515621 59454213382013858534179)
                  ·
                    rfl

theorem cell20_130260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_130260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130260 prefixEnd_130260 := by exact prefixLift 130260
  have htrace : WordTrace (prefixWord ++ tailWord_130260) baseStart_130260 baseEnd_130260 := by
    simpa [prefixWord, tailWord_130260, baseEnd_130260] using wordTrace_append hprefix tailTrace_130260
  have hstable : (prefixWord ++ tailWord_130260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130260).length < 2 ^ (prefixWord ++ tailWord_130260).sum := by decide
  have hdescent : baseEnd_130260 < baseStart_130260 := by decide
  rcases family_descends (prefixWord ++ tailWord_130260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130316 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_130316 : Nat := 118140960795 + 130316 * 2 ^ 59
def prefixEnd_130316 : Nat := 4983230072969 + 3 ^ 40 * 130316 * 2
def baseEnd_130316 : Nat := 59479773307926552667283

theorem tailTrace_130316 : CollatzResearch.WordTrace tailWord_130316 prefixEnd_130316 59479773307926552667283 := by
  unfold tailWord_130316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376507497947431523001401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3168676663929908697335201 2376507497947431523001401)
  ·
    refine ⟨1782380623460573642251051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2376507497947431523001401 1782380623460573642251051)
    ·
      refine ⟨2673570935190860463376577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782380623460573642251051 2673570935190860463376577)
      ·
        refine ⟨2005178201393145347532433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2673570935190860463376577 2005178201393145347532433)
        ·
          refine ⟨1503883651044859010649325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2005178201393145347532433 1503883651044859010649325)
          ·
            refine ⟨563956369141822128993497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1503883651044859010649325 563956369141822128993497)
            ·
              refine ⟨422967276856366596745123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563956369141822128993497 422967276856366596745123)
              ·
                refine ⟨634450915284549895117685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422967276856366596745123 634450915284549895117685)
                ·
                  refine ⟨59479773307926552667283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 634450915284549895117685 59479773307926552667283)
                  ·
                    rfl

theorem cell20_130316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_130316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130316 prefixEnd_130316 := by exact prefixLift 130316
  have htrace : WordTrace (prefixWord ++ tailWord_130316) baseStart_130316 baseEnd_130316 := by
    simpa [prefixWord, tailWord_130316, baseEnd_130316] using wordTrace_append hprefix tailTrace_130316
  have hstable : (prefixWord ++ tailWord_130316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130316).length < 2 ^ (prefixWord ++ tailWord_130316).sum := by decide
  have hdescent : baseEnd_130316 < baseStart_130316 := by decide
  rcases family_descends (prefixWord ++ tailWord_130316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130392 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_130392 : Nat := 118140960795 + 130392 * 2 ^ 59
def prefixEnd_130392 : Nat := 4983230072969 + 3 ^ 40 * 130392 * 2
def baseEnd_130392 : Nat := 59514461778808066133639

theorem tailTrace_130392 : CollatzResearch.WordTrace tailWord_130392 prefixEnd_130392 59514461778808066133639 := by
  unfold tailWord_130392
  simp only [CollatzResearch.WordTrace]
  refine ⟨2377893471809764012884715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3170524629079685350512953 2377893471809764012884715)
  ·
    refine ⟨3566840207714646019327073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2377893471809764012884715 3566840207714646019327073)
    ·
      refine ⟨2675130155785984514495305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3566840207714646019327073 2675130155785984514495305)
      ·
        refine ⟨2006347616839488385871479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2675130155785984514495305 2006347616839488385871479)
        ·
          refine ⟨3009521425259232578807219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2006347616839488385871479 3009521425259232578807219)
          ·
            refine ⟨4514282137888848868210829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009521425259232578807219 4514282137888848868210829)
            ·
              refine ⟨1692855801708318325579061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4514282137888848868210829 1692855801708318325579061)
              ·
                refine ⟨158705231410154843023037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1692855801708318325579061 158705231410154843023037)
                ·
                  refine ⟨59514461778808066133639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158705231410154843023037 59514461778808066133639)
                  ·
                    rfl

theorem cell20_130392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_130392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130392 prefixEnd_130392 := by exact prefixLift 130392
  have htrace : WordTrace (prefixWord ++ tailWord_130392) baseStart_130392 baseEnd_130392 := by
    simpa [prefixWord, tailWord_130392, baseEnd_130392] using wordTrace_append hprefix tailTrace_130392
  have hstable : (prefixWord ++ tailWord_130392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130392).length < 2 ^ (prefixWord ++ tailWord_130392).sum := by decide
  have hdescent : baseEnd_130392 < baseStart_130392 := by decide
  rcases family_descends (prefixWord ++ tailWord_130392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130402 : List Nat := [3, 3, 2, 1, 1, 1, 5, 4]
def baseStart_130402 : Nat := 118140960795 + 130402 * 2 ^ 59
def prefixEnd_130402 : Nat := 4983230072969 + 3 ^ 40 * 130402 * 2
def baseEnd_130402 : Nat := 19839675350430825266755

theorem tailTrace_130402 : CollatzResearch.WordTrace tailWord_130402 prefixEnd_130402 19839675350430825266755 := by
  unfold tailWord_130402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189037918395824933408365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3170767782388866489088973 1189037918395824933408365)
  ·
    refine ⟨445889219398434350028137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1189037918395824933408365 445889219398434350028137)
    ·
      refine ⟨334416914548825762521103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445889219398434350028137 334416914548825762521103)
      ·
        refine ⟨501625371823238643781655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334416914548825762521103 501625371823238643781655)
        ·
          refine ⟨752438057734857965672483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501625371823238643781655 752438057734857965672483)
          ·
            refine ⟨1128657086602286948508725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752438057734857965672483 1128657086602286948508725)
            ·
              refine ⟨105811601868964401422693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1128657086602286948508725 105811601868964401422693)
              ·
                refine ⟨19839675350430825266755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105811601868964401422693 19839675350430825266755)
                ·
                  rfl

theorem cell20_130402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_130402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130402 prefixEnd_130402 := by exact prefixLift 130402
  have htrace : WordTrace (prefixWord ++ tailWord_130402) baseStart_130402 baseEnd_130402 := by
    simpa [prefixWord, tailWord_130402, baseEnd_130402] using wordTrace_append hprefix tailTrace_130402
  have hstable : (prefixWord ++ tailWord_130402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130402).length < 2 ^ (prefixWord ++ tailWord_130402).sum := by decide
  have hdescent : baseEnd_130402 < baseStart_130402 := by decide
  rcases family_descends (prefixWord ++ tailWord_130402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130433 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 4]
def baseStart_130433 : Nat := 118140960795 + 130433 * 2 ^ 59
def prefixEnd_130433 : Nat := 4983230072969 + 3 ^ 40 * 130433 * 2
def baseEnd_130433 : Nat := 59533175295994145766805

theorem tailTrace_130433 : CollatzResearch.WordTrace tailWord_130433 prefixEnd_130433 59533175295994145766805 := by
  unfold tailWord_130433
  simp only [CollatzResearch.WordTrace]
  refine ⟨4757282336470992028011953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3171521557647328018674635 4757282336470992028011953)
  ·
    refine ⟨3567961752353244021008965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4757282336470992028011953 3567961752353244021008965)
    ·
      refine ⟨668992828566233253939181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3567961752353244021008965 668992828566233253939181)
      ·
        refine ⟨250872310712337470227193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668992828566233253939181 250872310712337470227193)
        ·
          refine ⟨188154233034253102670395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250872310712337470227193 188154233034253102670395)
          ·
            refine ⟨282231349551379654005593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188154233034253102670395 282231349551379654005593)
            ·
              refine ⟨211673512163534740504195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282231349551379654005593 211673512163534740504195)
              ·
                refine ⟨317510268245302110756293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211673512163534740504195 317510268245302110756293)
                ·
                  refine ⟨59533175295994145766805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317510268245302110756293 59533175295994145766805)
                  ·
                    rfl

theorem cell20_130433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_130433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130433 prefixEnd_130433 := by exact prefixLift 130433
  have htrace : WordTrace (prefixWord ++ tailWord_130433) baseStart_130433 baseEnd_130433 := by
    simpa [prefixWord, tailWord_130433, baseEnd_130433] using wordTrace_append hprefix tailTrace_130433
  have hstable : (prefixWord ++ tailWord_130433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130433).length < 2 ^ (prefixWord ++ tailWord_130433).sum := by decide
  have hdescent : baseEnd_130433 < baseStart_130433 := by decide
  rcases family_descends (prefixWord ++ tailWord_130433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130437 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_130437 : Nat := 118140960795 + 130437 * 2 ^ 59
def prefixEnd_130437 : Nat := 4983230072969 + 3 ^ 40 * 130437 * 2
def baseEnd_130437 : Nat := 59535001004987909633455

theorem tailTrace_130437 : CollatzResearch.WordTrace tailWord_130437 prefixEnd_130437 59535001004987909633455 := by
  unfold tailWord_130437
  simp only [CollatzResearch.WordTrace]
  refine ⟨4757428228456500711157565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3171618818971000474105043 4757428228456500711157565)
  ·
    refine ⟨1784035585671187766684087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4757428228456500711157565 1784035585671187766684087)
    ·
      refine ⟨2676053378506781650026131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1784035585671187766684087 2676053378506781650026131)
      ·
        refine ⟨4014080067760172475039197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676053378506781650026131 4014080067760172475039197)
        ·
          refine ⟨1505280025410064678139699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4014080067760172475039197 1505280025410064678139699)
          ·
            refine ⟨2257920038115097017209549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505280025410064678139699 2257920038115097017209549)
            ·
              refine ⟨846720014293161381453581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2257920038115097017209549 846720014293161381453581)
              ·
                refine ⟨317520005359935518045093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 846720014293161381453581 317520005359935518045093)
                ·
                  refine ⟨59535001004987909633455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317520005359935518045093 59535001004987909633455)
                  ·
                    rfl

theorem cell20_130437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_130437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130437 prefixEnd_130437 := by exact prefixLift 130437
  have htrace : WordTrace (prefixWord ++ tailWord_130437) baseStart_130437 baseEnd_130437 := by
    simpa [prefixWord, tailWord_130437, baseEnd_130437] using wordTrace_append hprefix tailTrace_130437
  have hstable : (prefixWord ++ tailWord_130437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130437).length < 2 ^ (prefixWord ++ tailWord_130437).sum := by decide
  have hdescent : baseEnd_130437 < baseStart_130437 := by decide
  rcases family_descends (prefixWord ++ tailWord_130437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130444 : List Nat := [2, 2, 1, 2, 1, 3, 2, 7]
def baseStart_130444 : Nat := 118140960795 + 130444 * 2 ^ 59
def prefixEnd_130444 : Nat := 4983230072969 + 3 ^ 40 * 130444 * 2
def baseEnd_130444 : Nat := 19846065331908998800031

theorem tailTrace_130444 : CollatzResearch.WordTrace tailWord_130444 prefixEnd_130444 19846065331908998800031 := by
  unfold tailWord_130444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378841769715570453331193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3171789026287427271108257 2378841769715570453331193)
  ·
    refine ⟨1784131327286677839998395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2378841769715570453331193 1784131327286677839998395)
    ·
      refine ⟨2676196990930016759997593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1784131327286677839998395 2676196990930016759997593)
      ·
        refine ⟨2007147743197512569998195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2676196990930016759997593 2007147743197512569998195)
        ·
          refine ⟨3010721614796268854997293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007147743197512569998195 3010721614796268854997293)
          ·
            refine ⟨1129020605548600820623985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3010721614796268854997293 1129020605548600820623985)
            ·
              refine ⟨846765454161450615467989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129020605548600820623985 846765454161450615467989)
              ·
                refine ⟨19846065331908998800031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 846765454161450615467989 19846065331908998800031)
                ·
                  rfl

theorem cell20_130444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_130444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130444 prefixEnd_130444 := by exact prefixLift 130444
  have htrace : WordTrace (prefixWord ++ tailWord_130444) baseStart_130444 baseEnd_130444 := by
    simpa [prefixWord, tailWord_130444, baseEnd_130444] using wordTrace_append hprefix tailTrace_130444
  have hstable : (prefixWord ++ tailWord_130444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130444).length < 2 ^ (prefixWord ++ tailWord_130444).sum := by decide
  have hdescent : baseEnd_130444 < baseStart_130444 := by decide
  rcases family_descends (prefixWord ++ tailWord_130444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130461 : List Nat := [1, 4, 2, 1, 3, 2, 1, 6]
def baseStart_130461 : Nat := 118140960795 + 130461 * 2 ^ 59
def prefixEnd_130461 : Nat := 4983230072969 + 3 ^ 40 * 130461 * 2
def baseEnd_130461 : Nat := 19848651752983497611119

theorem tailTrace_130461 : CollatzResearch.WordTrace tailWord_130461 prefixEnd_130461 19848651752983497611119 := by
  unfold tailWord_130461
  simp only [CollatzResearch.WordTrace]
  refine ⟨4758303580369552810031237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3172202386913035206687491 4758303580369552810031237)
  ·
    refine ⟨892181921319291151880857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4758303580369552810031237 892181921319291151880857)
    ·
      refine ⟨669136440989468363910643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 892181921319291151880857 669136440989468363910643)
      ·
        refine ⟨1003704661484202545865965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669136440989468363910643 1003704661484202545865965)
        ·
          refine ⟨376389248056575954699737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003704661484202545865965 376389248056575954699737)
          ·
            refine ⟨282291936042431966024803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376389248056575954699737 282291936042431966024803)
            ·
              refine ⟨423437904063647949037205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282291936042431966024803 423437904063647949037205)
              ·
                refine ⟨19848651752983497611119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 423437904063647949037205 19848651752983497611119)
                ·
                  rfl

theorem cell20_130461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 6].length) (baseStart_130461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130461 prefixEnd_130461 := by exact prefixLift 130461
  have htrace : WordTrace (prefixWord ++ tailWord_130461) baseStart_130461 baseEnd_130461 := by
    simpa [prefixWord, tailWord_130461, baseEnd_130461] using wordTrace_append hprefix tailTrace_130461
  have hstable : (prefixWord ++ tailWord_130461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130461).length < 2 ^ (prefixWord ++ tailWord_130461).sum := by decide
  have hdescent : baseEnd_130461 < baseStart_130461 := by decide
  rcases family_descends (prefixWord ++ tailWord_130461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130520 : List Nat := [2, 1, 2, 2, 2, 1, 4, 6]
def baseStart_130520 : Nat := 118140960795 + 130520 * 2 ^ 59
def prefixEnd_130520 : Nat := 4983230072969 + 3 ^ 40 * 130520 * 2
def baseEnd_130520 : Nat := 19857628155536169955483

theorem tailTrace_130520 : CollatzResearch.WordTrace tailWord_130520 prefixEnd_130520 19857628155536169955483 := by
  unfold tailWord_130520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2380227743577902943214507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3173636991437203924286009 2380227743577902943214507)
  ·
    refine ⟨3570341615366854414821761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2380227743577902943214507 3570341615366854414821761)
    ·
      refine ⟨2677756211525140811116321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3570341615366854414821761 2677756211525140811116321)
      ·
        refine ⟨2008317158643855608337241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2677756211525140811116321 2008317158643855608337241)
        ·
          refine ⟨1506237868982891706252931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2008317158643855608337241 1506237868982891706252931)
          ·
            refine ⟨2259356803474337559379397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506237868982891706252931 2259356803474337559379397)
            ·
              refine ⟨423629400651438292383637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2259356803474337559379397 423629400651438292383637)
              ·
                refine ⟨19857628155536169955483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 423629400651438292383637 19857628155536169955483)
                ·
                  rfl

theorem cell20_130520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_130520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130520 prefixEnd_130520 := by exact prefixLift 130520
  have htrace : WordTrace (prefixWord ++ tailWord_130520) baseStart_130520 baseEnd_130520 := by
    simpa [prefixWord, tailWord_130520, baseEnd_130520] using wordTrace_append hprefix tailTrace_130520
  have hstable : (prefixWord ++ tailWord_130520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130520).length < 2 ^ (prefixWord ++ tailWord_130520).sum := by decide
  have hdescent : baseEnd_130520 < baseStart_130520 := by decide
  rcases family_descends (prefixWord ++ tailWord_130520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130544 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_130544 : Nat := 118140960795 + 130544 * 2 ^ 59
def prefixEnd_130544 : Nat := 4983230072969 + 3 ^ 40 * 130544 * 2
def baseEnd_130544 : Nat := 59583838720571093066351

theorem tailTrace_130544 : CollatzResearch.WordTrace tailWord_130544 prefixEnd_130544 59583838720571093066351 := by
  unfold tailWord_130544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2380665419534428992651343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3174220559379238656868457 2380665419534428992651343)
  ·
    refine ⟨3570998129301643488977015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2380665419534428992651343 3570998129301643488977015)
    ·
      refine ⟨5356497193952465233465523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3570998129301643488977015 5356497193952465233465523)
      ·
        refine ⟨8034745790928697850198285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5356497193952465233465523 8034745790928697850198285)
        ·
          refine ⟨3013029671598261693824357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8034745790928697850198285 3013029671598261693824357)
          ·
            refine ⟨564943063424674067592067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3013029671598261693824357 564943063424674067592067)
            ·
              refine ⟨847414595137011101388101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564943063424674067592067 847414595137011101388101)
              ·
                refine ⟨158890236588189581510269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847414595137011101388101 158890236588189581510269)
                ·
                  refine ⟨59583838720571093066351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158890236588189581510269 59583838720571093066351)
                  ·
                    rfl

theorem cell20_130544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_130544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130544 prefixEnd_130544 := by exact prefixLift 130544
  have htrace : WordTrace (prefixWord ++ tailWord_130544) baseStart_130544 baseEnd_130544 := by
    simpa [prefixWord, tailWord_130544, baseEnd_130544] using wordTrace_append hprefix tailTrace_130544
  have hstable : (prefixWord ++ tailWord_130544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130544).length < 2 ^ (prefixWord ++ tailWord_130544).sum := by decide
  have hdescent : baseEnd_130544 < baseStart_130544 := by decide
  rcases family_descends (prefixWord ++ tailWord_130544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130565 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_130565 : Nat := 118140960795 + 130565 * 2 ^ 59
def prefixEnd_130565 : Nat := 4983230072969 + 3 ^ 40 * 130565 * 2
def baseEnd_130565 : Nat := 59593423692788353366265

theorem tailTrace_130565 : CollatzResearch.WordTrace tailWord_130565 prefixEnd_130565 59593423692788353366265 := by
  unfold tailWord_130565
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762096771992778571817149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3174731181328519047878099 4762096771992778571817149)
  ·
    refine ⟨1785786289497291964431431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4762096771992778571817149 1785786289497291964431431)
    ·
      refine ⟨2678679434245937946647147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785786289497291964431431 2678679434245937946647147)
      ·
        refine ⟨4018019151368906919970721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678679434245937946647147 4018019151368906919970721)
        ·
          refine ⟨3013514363526680189978041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4018019151368906919970721 3013514363526680189978041)
          ·
            refine ⟨2260135772645010142483531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3013514363526680189978041 2260135772645010142483531)
            ·
              refine ⟨3390203658967515213725297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2260135772645010142483531 3390203658967515213725297)
              ·
                refine ⟨2542652744225636410293973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3390203658967515213725297 2542652744225636410293973)
                ·
                  refine ⟨59593423692788353366265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2542652744225636410293973 59593423692788353366265)
                  ·
                    rfl

theorem cell20_130565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_130565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130565 prefixEnd_130565 := by exact prefixLift 130565
  have htrace : WordTrace (prefixWord ++ tailWord_130565) baseStart_130565 baseEnd_130565 := by
    simpa [prefixWord, tailWord_130565, baseEnd_130565] using wordTrace_append hprefix tailTrace_130565
  have hstable : (prefixWord ++ tailWord_130565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130565).length < 2 ^ (prefixWord ++ tailWord_130565).sum := by decide
  have hdescent : baseEnd_130565 < baseStart_130565 := by decide
  rcases family_descends (prefixWord ++ tailWord_130565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130589 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_130589 : Nat := 118140960795 + 130589 * 2 ^ 59
def prefixEnd_130589 : Nat := 4983230072969 + 3 ^ 40 * 130589 * 2
def baseEnd_130589 : Nat := 59604377946750936566167

theorem tailTrace_130589 : CollatzResearch.WordTrace tailWord_130589 prefixEnd_130589 59604377946750936566167 := by
  unfold tailWord_130589
  simp only [CollatzResearch.WordTrace]
  refine ⟨4762972123905830670690821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3175314749270553780460547 4762972123905830670690821)
  ·
    refine ⟨893057273232343250754529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4762972123905830670690821 893057273232343250754529)
    ·
      refine ⟨669792954924257438065897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 893057273232343250754529 669792954924257438065897)
      ·
        refine ⟨502344716193193078549423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669792954924257438065897 502344716193193078549423)
        ·
          refine ⟨753517074289789617824135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502344716193193078549423 753517074289789617824135)
          ·
            refine ⟨1130275611434684426736203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753517074289789617824135 1130275611434684426736203)
            ·
              refine ⟨1695413417152026640104305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130275611434684426736203 1695413417152026640104305)
              ·
                refine ⟨1271560062864019980078229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695413417152026640104305 1271560062864019980078229)
                ·
                  refine ⟨59604377946750936566167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1271560062864019980078229 59604377946750936566167)
                  ·
                    rfl

theorem cell20_130589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_130589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130589 prefixEnd_130589 := by exact prefixLift 130589
  have htrace : WordTrace (prefixWord ++ tailWord_130589) baseStart_130589 baseEnd_130589 := by
    simpa [prefixWord, tailWord_130589, baseEnd_130589] using wordTrace_append hprefix tailTrace_130589
  have hstable : (prefixWord ++ tailWord_130589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130589).length < 2 ^ (prefixWord ++ tailWord_130589).sum := by decide
  have hdescent : baseEnd_130589 < baseStart_130589 := by decide
  rcases family_descends (prefixWord ++ tailWord_130589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130606 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_130606 : Nat := 118140960795 + 130606 * 2 ^ 59
def prefixEnd_130606 : Nat := 4983230072969 + 3 ^ 40 * 130606 * 2
def baseEnd_130606 : Nat := 59612137209974432999431

theorem tailTrace_130606 : CollatzResearch.WordTrace tailWord_130606 prefixEnd_130606 59612137209974432999431 := by
  unfold tailWord_130606
  simp only [CollatzResearch.WordTrace]
  refine ⟨595449020605530321757459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3175728109896161716039781 595449020605530321757459)
  ·
    refine ⟨893173530908295482636189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 595449020605530321757459 893173530908295482636189)
    ·
      refine ⟨334940074090610805988571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 893173530908295482636189 334940074090610805988571)
      ·
        refine ⟨502410111135916208982857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334940074090610805988571 502410111135916208982857)
        ·
          refine ⟨376807583351937156737143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502410111135916208982857 376807583351937156737143)
          ·
            refine ⟨565211375027905735105715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376807583351937156737143 565211375027905735105715)
            ·
              refine ⟨847817062541858602658573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565211375027905735105715 847817062541858602658573)
              ·
                refine ⟨317931398453196975996965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 847817062541858602658573 317931398453196975996965)
                ·
                  refine ⟨59612137209974432999431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317931398453196975996965 59612137209974432999431)
                  ·
                    rfl

theorem cell20_130606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_130606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130606 prefixEnd_130606 := by exact prefixLift 130606
  have htrace : WordTrace (prefixWord ++ tailWord_130606) baseStart_130606 baseEnd_130606 := by
    simpa [prefixWord, tailWord_130606, baseEnd_130606] using wordTrace_append hprefix tailTrace_130606
  have hstable : (prefixWord ++ tailWord_130606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130606).length < 2 ^ (prefixWord ++ tailWord_130606).sum := by decide
  have hdescent : baseEnd_130606 < baseStart_130606 := by decide
  rcases family_descends (prefixWord ++ tailWord_130606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130634 : List Nat := [3, 1, 2, 1, 1, 3, 3, 6]
def baseStart_130634 : Nat := 118140960795 + 130634 * 2 ^ 59
def prefixEnd_130634 : Nat := 4983230072969 + 3 ^ 40 * 130634 * 2
def baseEnd_130634 : Nat := 19874972390976926688661

theorem tailTrace_130634 : CollatzResearch.WordTrace tailWord_130634 prefixEnd_130634 19874972390976926688661 := by
  unfold tailWord_130634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191153352185700839019739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3176408939161868904052637 1191153352185700839019739)
  ·
    refine ⟨1786730028278551258529609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1191153352185700839019739 1786730028278551258529609)
    ·
      refine ⟨1340047521208913443897207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1786730028278551258529609 1340047521208913443897207)
      ·
        refine ⟨2010071281813370165845811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340047521208913443897207 2010071281813370165845811)
        ·
          refine ⟨3015106922720055248768717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010071281813370165845811 3015106922720055248768717)
          ·
            refine ⟨1130665096020020718288269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3015106922720055248768717 1130665096020020718288269)
            ·
              refine ⟨423999411007507769358101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1130665096020020718288269 423999411007507769358101)
              ·
                refine ⟨19874972390976926688661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 423999411007507769358101 19874972390976926688661)
                ·
                  rfl

theorem cell20_130634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_130634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130634 prefixEnd_130634 := by exact prefixLift 130634
  have htrace : WordTrace (prefixWord ++ tailWord_130634) baseStart_130634 baseEnd_130634 := by
    simpa [prefixWord, tailWord_130634, baseEnd_130634] using wordTrace_append hprefix tailTrace_130634
  have hstable : (prefixWord ++ tailWord_130634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130634).length < 2 ^ (prefixWord ++ tailWord_130634).sum := by decide
  have hdescent : baseEnd_130634 < baseStart_130634 := by decide
  rcases family_descends (prefixWord ++ tailWord_130634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130641 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_130641 : Nat := 118140960795 + 130641 * 2 ^ 59
def prefixEnd_130641 : Nat := 4983230072969 + 3 ^ 40 * 130641 * 2
def baseEnd_130641 : Nat := 59628112163669866832621

theorem tailTrace_130641 : CollatzResearch.WordTrace tailWord_130641 prefixEnd_130641 59628112163669866832621 := by
  unfold tailWord_130641
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764868719717443551583777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3176579146478295701055851 4764868719717443551583777)
  ·
    refine ⟨3573651539788082663687833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4764868719717443551583777 3573651539788082663687833)
    ·
      refine ⟨2680238654841061997765875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3573651539788082663687833 2680238654841061997765875)
      ·
        refine ⟨4020357982261592996648813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2680238654841061997765875 4020357982261592996648813)
        ·
          refine ⟨1507634243348097373743305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4020357982261592996648813 1507634243348097373743305)
          ·
            refine ⟨1130725682511073030307479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1507634243348097373743305 1130725682511073030307479)
            ·
              refine ⟨1696088523766609545461219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130725682511073030307479 1696088523766609545461219)
              ·
                refine ⟨2544132785649914318191829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1696088523766609545461219 2544132785649914318191829)
                ·
                  refine ⟨59628112163669866832621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2544132785649914318191829 59628112163669866832621)
                  ·
                    rfl

theorem cell20_130641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_130641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130641 prefixEnd_130641 := by exact prefixLift 130641
  have htrace : WordTrace (prefixWord ++ tailWord_130641) baseStart_130641 baseEnd_130641 := by
    simpa [prefixWord, tailWord_130641, baseEnd_130641] using wordTrace_append hprefix tailTrace_130641
  have hstable : (prefixWord ++ tailWord_130641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130641).length < 2 ^ (prefixWord ++ tailWord_130641).sum := by decide
  have hdescent : baseEnd_130641 < baseStart_130641 := by decide
  rcases family_descends (prefixWord ++ tailWord_130641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130665 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 4]
def baseStart_130665 : Nat := 118140960795 + 130665 * 2 ^ 59
def prefixEnd_130665 : Nat := 4983230072969 + 3 ^ 40 * 130665 * 2
def baseEnd_130665 : Nat := 59639066417632450032523

theorem tailTrace_130665 : CollatzResearch.WordTrace tailWord_130665 prefixEnd_130665 59639066417632450032523 := by
  unfold tailWord_130665
  simp only [CollatzResearch.WordTrace]
  refine ⟨4765744071630495650457449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3177162714420330433638299 4765744071630495650457449)
  ·
    refine ⟨3574308053722871737843087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4765744071630495650457449 3574308053722871737843087)
    ·
      refine ⟨5361462080584307606764631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3574308053722871737843087 5361462080584307606764631)
      ·
        refine ⟨8042193120876461410146947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361462080584307606764631 8042193120876461410146947)
        ·
          refine ⟨12063289681314692115220421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042193120876461410146947 12063289681314692115220421)
          ·
            refine ⟨2261866815246504771603829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12063289681314692115220421 2261866815246504771603829)
            ·
              refine ⟨212050013929359822337859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2261866815246504771603829 212050013929359822337859)
              ·
                refine ⟨318075020894039733506789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212050013929359822337859 318075020894039733506789)
                ·
                  refine ⟨59639066417632450032523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 318075020894039733506789 59639066417632450032523)
                  ·
                    rfl

theorem cell20_130665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_130665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130665 prefixEnd_130665 := by exact prefixLift 130665
  have htrace : WordTrace (prefixWord ++ tailWord_130665) baseStart_130665 baseEnd_130665 := by
    simpa [prefixWord, tailWord_130665, baseEnd_130665] using wordTrace_append hprefix tailTrace_130665
  have hstable : (prefixWord ++ tailWord_130665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130665).length < 2 ^ (prefixWord ++ tailWord_130665).sum := by decide
  have hdescent : baseEnd_130665 < baseStart_130665 := by decide
  rcases family_descends (prefixWord ++ tailWord_130665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130672 : List Nat := [2, 1, 1, 1, 6, 1, 1, 7]
def baseStart_130672 : Nat := 118140960795 + 130672 * 2 ^ 59
def prefixEnd_130672 : Nat := 4983230072969 + 3 ^ 40 * 130672 * 2
def baseEnd_130672 : Nat := 19880753802790512266387

theorem tailTrace_130672 : CollatzResearch.WordTrace tailWord_130672 prefixEnd_130672 19880753802790512266387 := by
  unfold tailWord_130672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2382999691302567922981135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3177332921736757230641513 2382999691302567922981135)
  ·
    refine ⟨3574499536953851884471703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2382999691302567922981135 3574499536953851884471703)
    ·
      refine ⟨5361749305430777826707555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3574499536953851884471703 5361749305430777826707555)
      ·
        refine ⟨8042623958146166740061333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361749305430777826707555 8042623958146166740061333)
        ·
          refine ⟨376997998038101565940375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8042623958146166740061333 376997998038101565940375)
          ·
            refine ⟨565496997057152348910563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376997998038101565940375 565496997057152348910563)
            ·
              refine ⟨848245495585728523365845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565496997057152348910563 848245495585728523365845)
              ·
                refine ⟨19880753802790512266387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 848245495585728523365845 19880753802790512266387)
                ·
                  rfl

theorem cell20_130672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_130672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130672 prefixEnd_130672 := by exact prefixLift 130672
  have htrace : WordTrace (prefixWord ++ tailWord_130672) baseStart_130672 baseEnd_130672 := by
    simpa [prefixWord, tailWord_130672, baseEnd_130672] using wordTrace_append hprefix tailTrace_130672
  have hstable : (prefixWord ++ tailWord_130672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130672).length < 2 ^ (prefixWord ++ tailWord_130672).sum := by decide
  have hdescent : baseEnd_130672 < baseStart_130672 := by decide
  rcases family_descends (prefixWord ++ tailWord_130672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130789 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 3]
def baseStart_130789 : Nat := 118140960795 + 130789 * 2 ^ 59
def prefixEnd_130789 : Nat := 4983230072969 + 3 ^ 40 * 130789 * 2
def baseEnd_130789 : Nat := 59695663396439129898683

theorem tailTrace_130789 : CollatzResearch.WordTrace tailWord_130789 prefixEnd_130789 59695663396439129898683 := by
  unfold tailWord_130789
  simp only [CollatzResearch.WordTrace]
  refine ⟨4770266723181264827971421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3180177815454176551980947 4770266723181264827971421)
  ·
    refine ⟨1788850021192974310489283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4770266723181264827971421 1788850021192974310489283)
    ·
      refine ⟨2683275031789461465733925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1788850021192974310489283 2683275031789461465733925)
      ·
        refine ⟨503114068460524024825111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2683275031789461465733925 503114068460524024825111)
        ·
          refine ⟨754671102690786037237667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503114068460524024825111 754671102690786037237667)
          ·
            refine ⟨1132006654036179055856501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754671102690786037237667 1132006654036179055856501)
            ·
              refine ⟨106125623815891786486547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1132006654036179055856501 106125623815891786486547)
              ·
                refine ⟨159188435723837679729821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106125623815891786486547 159188435723837679729821)
                ·
                  refine ⟨59695663396439129898683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159188435723837679729821 59695663396439129898683)
                  ·
                    rfl

theorem cell20_130789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_130789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130789 prefixEnd_130789 := by exact prefixLift 130789
  have htrace : WordTrace (prefixWord ++ tailWord_130789) baseStart_130789 baseEnd_130789 := by
    simpa [prefixWord, tailWord_130789, baseEnd_130789] using wordTrace_append hprefix tailTrace_130789
  have hstable : (prefixWord ++ tailWord_130789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130789).length < 2 ^ (prefixWord ++ tailWord_130789).sum := by decide
  have hdescent : baseEnd_130789 < baseStart_130789 := by decide
  rcases family_descends (prefixWord ++ tailWord_130789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130800 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_130800 : Nat := 118140960795 + 130800 * 2 ^ 59
def prefixEnd_130800 : Nat := 4983230072969 + 3 ^ 40 * 130800 * 2
def baseEnd_130800 : Nat := 59700684096171980531971

theorem tailTrace_130800 : CollatzResearch.WordTrace tailWord_130800 prefixEnd_130800 59700684096171980531971 := by
  unfold tailWord_130800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385333963070706853310927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3180445284094275804414569 2385333963070706853310927)
  ·
    refine ⟨3578000944606060279966391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2385333963070706853310927 3578000944606060279966391)
    ·
      refine ⟨5367001416909090419949587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3578000944606060279966391 5367001416909090419949587)
      ·
        refine ⟨8050502125363635629924381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5367001416909090419949587 8050502125363635629924381)
        ·
          refine ⟨3018938297011363361221643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8050502125363635629924381 3018938297011363361221643)
          ·
            refine ⟨4528407445517045041832465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018938297011363361221643 4528407445517045041832465)
            ·
              refine ⟨3396305584137783781374349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528407445517045041832465 3396305584137783781374349)
              ·
                refine ⟨1273614594051668918015381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3396305584137783781374349 1273614594051668918015381)
                ·
                  refine ⟨59700684096171980531971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1273614594051668918015381 59700684096171980531971)
                  ·
                    rfl

theorem cell20_130800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_130800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130800 prefixEnd_130800 := by exact prefixLift 130800
  have htrace : WordTrace (prefixWord ++ tailWord_130800) baseStart_130800 baseEnd_130800 := by
    simpa [prefixWord, tailWord_130800, baseEnd_130800] using wordTrace_append hprefix tailTrace_130800
  have hstable : (prefixWord ++ tailWord_130800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130800).length < 2 ^ (prefixWord ++ tailWord_130800).sum := by decide
  have hdescent : baseEnd_130800 < baseStart_130800 := by decide
  rcases family_descends (prefixWord ++ tailWord_130800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130822 : List Nat := [6, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_130822 : Nat := 118140960795 + 130822 * 2 ^ 59
def prefixEnd_130822 : Nat := 4983230072969 + 3 ^ 40 * 130822 * 2
def baseEnd_130822 : Nat := 59710725495637681798549

theorem tailTrace_130822 : CollatzResearch.WordTrace tailWord_130822 prefixEnd_130822 59710725495637681798549 := by
  unfold tailWord_130822
  simp only [CollatzResearch.WordTrace]
  refine ⟨149108447876928483247585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3180980221374474309281813 149108447876928483247585)
  ·
    refine ⟨111831335907696362435689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149108447876928483247585 111831335907696362435689)
    ·
      refine ⟨83873501930772271826767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111831335907696362435689 83873501930772271826767)
      ·
        refine ⟨125810252896158407740151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83873501930772271826767 125810252896158407740151)
        ·
          refine ⟨188715379344237611610227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125810252896158407740151 188715379344237611610227)
          ·
            refine ⟨283073069016356417415341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188715379344237611610227 283073069016356417415341)
            ·
              refine ⟨106152400881133656530753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283073069016356417415341 106152400881133656530753)
              ·
                refine ⟨79614300660850242398065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106152400881133656530753 79614300660850242398065)
                ·
                  refine ⟨59710725495637681798549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79614300660850242398065 59710725495637681798549)
                  ·
                    rfl

theorem cell20_130822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_130822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130822 prefixEnd_130822 := by exact prefixLift 130822
  have htrace : WordTrace (prefixWord ++ tailWord_130822) baseStart_130822 baseEnd_130822 := by
    simpa [prefixWord, tailWord_130822, baseEnd_130822] using wordTrace_append hprefix tailTrace_130822
  have hstable : (prefixWord ++ tailWord_130822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130822).length < 2 ^ (prefixWord ++ tailWord_130822).sum := by decide
  have hdescent : baseEnd_130822 < baseStart_130822 := by decide
  rcases family_descends (prefixWord ++ tailWord_130822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130848 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 3]
def baseStart_130848 : Nat := 118140960795 + 130848 * 2 ^ 59
def prefixEnd_130848 : Nat := 4983230072969 + 3 ^ 40 * 130848 * 2
def baseEnd_130848 : Nat := 59722592604097146931775

theorem tailTrace_130848 : CollatzResearch.WordTrace tailWord_130848 prefixEnd_130848 59722592604097146931775 := by
  unfold tailWord_130848
  simp only [CollatzResearch.WordTrace]
  refine ⟨2386209314983758952184599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3181612419978345269579465 2386209314983758952184599)
  ·
    refine ⟨3579313972475638428276899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2386209314983758952184599 3579313972475638428276899)
    ·
      refine ⟨5368970958713457642415349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3579313972475638428276899 5368970958713457642415349)
      ·
        refine ⟨503341027379386653976439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5368970958713457642415349 503341027379386653976439)
        ·
          refine ⟨755011541069079980964659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503341027379386653976439 755011541069079980964659)
          ·
            refine ⟨1132517311603619971446989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755011541069079980964659 1132517311603619971446989)
            ·
              refine ⟨424693991851357489292621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1132517311603619971446989 424693991851357489292621)
              ·
                refine ⟨159260246944259058484733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424693991851357489292621 159260246944259058484733)
                ·
                  refine ⟨59722592604097146931775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159260246944259058484733 59722592604097146931775)
                  ·
                    rfl

theorem cell20_130848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_130848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130848 prefixEnd_130848 := by exact prefixLift 130848
  have htrace : WordTrace (prefixWord ++ tailWord_130848) baseStart_130848 baseEnd_130848 := by
    simpa [prefixWord, tailWord_130848, baseEnd_130848] using wordTrace_append hprefix tailTrace_130848
  have hstable : (prefixWord ++ tailWord_130848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130848).length < 2 ^ (prefixWord ++ tailWord_130848).sum := by decide
  have hdescent : baseEnd_130848 < baseStart_130848 := by decide
  rcases family_descends (prefixWord ++ tailWord_130848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130883 : List Nat := [1, 1, 1, 3, 1, 13]
def baseStart_130883 : Nat := 118140960795 + 130883 * 2 ^ 59
def prefixEnd_130883 : Nat := 4983230072969 + 3 ^ 40 * 130883 * 2
def baseEnd_130883 : Nat := 2212539539177502991295

theorem tailTrace_130883 : CollatzResearch.WordTrace tailWord_130883 prefixEnd_130883 2212539539177502991295 := by
  unfold tailWord_130883
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773695184840718881893303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3182463456560479254595535 4773695184840718881893303)
  ·
    refine ⟨7160542777261078322839955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4773695184840718881893303 7160542777261078322839955)
    ·
      refine ⟨10740814165891617484259933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160542777261078322839955 10740814165891617484259933)
      ·
        refine ⟨4027805312209356556597475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10740814165891617484259933 4027805312209356556597475)
        ·
          refine ⟨6041707968314034834896213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4027805312209356556597475 6041707968314034834896213)
          ·
            refine ⟨2212539539177502991295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 6041707968314034834896213 2212539539177502991295)
            ·
              rfl

theorem cell20_130883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 13].length) (baseStart_130883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130883 prefixEnd_130883 := by exact prefixLift 130883
  have htrace : WordTrace (prefixWord ++ tailWord_130883) baseStart_130883 baseEnd_130883 := by
    simpa [prefixWord, tailWord_130883, baseEnd_130883] using wordTrace_append hprefix tailTrace_130883
  have hstable : (prefixWord ++ tailWord_130883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130883).length < 2 ^ (prefixWord ++ tailWord_130883).sum := by decide
  have hdescent : baseEnd_130883 < baseStart_130883 := by decide
  rcases family_descends (prefixWord ++ tailWord_130883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130921 : List Nat := [1, 2, 1, 1, 1, 3, 1, 10]
def baseStart_130921 : Nat := 118140960795 + 130921 * 2 ^ 59
def prefixEnd_130921 : Nat := 4983230072969 + 3 ^ 40 * 130921 * 2
def baseEnd_130921 : Nat := 19918637264411112499381

theorem tailTrace_130921 : CollatzResearch.WordTrace tailWord_130921 prefixEnd_130921 19918637264411112499381 := by
  unfold tailWord_130921
  simp only [CollatzResearch.WordTrace]
  refine ⟨4775081158703051371776617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3183387439135367581184411 4775081158703051371776617)
  ·
    refine ⟨3581310869027288528832463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4775081158703051371776617 3581310869027288528832463)
    ·
      refine ⟨5371966303540932793248695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581310869027288528832463 5371966303540932793248695)
      ·
        refine ⟨8057949455311399189873043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371966303540932793248695 8057949455311399189873043)
        ·
          refine ⟨12086924182967098784809565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057949455311399189873043 12086924182967098784809565)
          ·
            refine ⟨4532596568612662044303587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12086924182967098784809565 4532596568612662044303587)
            ·
              refine ⟨6798894852918993066455381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532596568612662044303587 6798894852918993066455381)
              ·
                refine ⟨19918637264411112499381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6798894852918993066455381 19918637264411112499381)
                ·
                  rfl

theorem cell20_130921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_130921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130921 prefixEnd_130921 := by exact prefixLift 130921
  have htrace : WordTrace (prefixWord ++ tailWord_130921) baseStart_130921 baseEnd_130921 := by
    simpa [prefixWord, tailWord_130921, baseEnd_130921] using wordTrace_append hprefix tailTrace_130921
  have hstable : (prefixWord ++ tailWord_130921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130921).length < 2 ^ (prefixWord ++ tailWord_130921).sum := by decide
  have hdescent : baseEnd_130921 < baseStart_130921 := by decide
  rcases family_descends (prefixWord ++ tailWord_130921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130948 : List Nat := [2, 3, 2, 1, 1, 1, 4, 4, 2]
def baseStart_130948 : Nat := 118140960795 + 130948 * 2 ^ 59
def prefixEnd_130948 : Nat := 4983230072969 + 3 ^ 40 * 130948 * 2
def baseEnd_130948 : Nat := 59768235328941243598033

theorem tailTrace_130948 : CollatzResearch.WordTrace tailWord_130948 prefixEnd_130948 59768235328941243598033 := by
  unfold tailWord_130948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388032964802617491504749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3184043953070156655339665 2388032964802617491504749)
  ·
    refine ⟨895512361800981559314281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2388032964802617491504749 895512361800981559314281)
    ·
      refine ⟨671634271350736169485711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 895512361800981559314281 671634271350736169485711)
      ·
        refine ⟨1007451407026104254228567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671634271350736169485711 1007451407026104254228567)
        ·
          refine ⟨1511177110539156381342851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007451407026104254228567 1511177110539156381342851)
          ·
            refine ⟨2266765665808734572014277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511177110539156381342851 2266765665808734572014277)
            ·
              refine ⟨425018562339137732252677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2266765665808734572014277 425018562339137732252677)
              ·
                refine ⟨79690980438588324797377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425018562339137732252677 79690980438588324797377)
                ·
                  refine ⟨59768235328941243598033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79690980438588324797377 59768235328941243598033)
                  ·
                    rfl

theorem cell20_130948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_130948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130948 prefixEnd_130948 := by exact prefixLift 130948
  have htrace : WordTrace (prefixWord ++ tailWord_130948) baseStart_130948 baseEnd_130948 := by
    simpa [prefixWord, tailWord_130948, baseEnd_130948] using wordTrace_append hprefix tailTrace_130948
  have hstable : (prefixWord ++ tailWord_130948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130948).length < 2 ^ (prefixWord ++ tailWord_130948).sum := by decide
  have hdescent : baseEnd_130948 < baseStart_130948 := by decide
  rcases family_descends (prefixWord ++ tailWord_130948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130972 : List Nat := [2, 2, 3, 3, 1, 3, 2, 4]
def baseStart_130972 : Nat := 118140960795 + 130972 * 2 ^ 59
def prefixEnd_130972 : Nat := 4983230072969 + 3 ^ 40 * 130972 * 2
def baseEnd_130972 : Nat := 19926396527634608932645

theorem tailTrace_130972 : CollatzResearch.WordTrace tailWord_130972 prefixEnd_130972 19926396527634608932645 := by
  unfold tailWord_130972
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388470640759143540941585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3184627521012191387922113 2388470640759143540941585)
  ·
    refine ⟨1791352980569357655706189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2388470640759143540941585 1791352980569357655706189)
    ·
      refine ⟨671757367713509120889821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1791352980569357655706189 671757367713509120889821)
      ·
        refine ⟨251909012892565920333683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 671757367713509120889821 251909012892565920333683)
        ·
          refine ⟨377863519338848880500525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251909012892565920333683 377863519338848880500525)
          ·
            refine ⟨141698819752068330187697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377863519338848880500525 141698819752068330187697)
            ·
              refine ⟨106274114814051247640773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141698819752068330187697 106274114814051247640773)
              ·
                refine ⟨19926396527634608932645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106274114814051247640773 19926396527634608932645)
                ·
                  rfl

theorem cell20_130972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_130972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_130972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_130972 prefixEnd_130972 := by exact prefixLift 130972
  have htrace : WordTrace (prefixWord ++ tailWord_130972) baseStart_130972 baseEnd_130972 := by
    simpa [prefixWord, tailWord_130972, baseEnd_130972] using wordTrace_append hprefix tailTrace_130972
  have hstable : (prefixWord ++ tailWord_130972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130972).length < 2 ^ (prefixWord ++ tailWord_130972).sum := by decide
  have hdescent : baseEnd_130972 < baseStart_130972 := by decide
  rcases family_descends (prefixWord ++ tailWord_130972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131100 : List Nat := [2, 2, 3, 1, 3, 1, 1, 5, 2]
def baseStart_131100 : Nat := 118140960795 + 131100 * 2 ^ 59
def prefixEnd_131100 : Nat := 4983230072969 + 3 ^ 40 * 131100 * 2
def baseEnd_131100 : Nat := 59837612270704270530745

theorem tailTrace_131100 : CollatzResearch.WordTrace tailWord_131100 prefixEnd_131100 59837612270704270530745 := by
  unfold tailWord_131100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2390804912527282471271377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3187739883369709961695169 2390804912527282471271377)
  ·
    refine ⟨1793103684395461853453533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2390804912527282471271377 1793103684395461853453533)
    ·
      refine ⟨672413881648298195045075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1793103684395461853453533 672413881648298195045075)
      ·
        refine ⟨1008620822472447292567613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672413881648298195045075 1008620822472447292567613)
        ·
          refine ⟨378232808427167734712855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1008620822472447292567613 378232808427167734712855)
          ·
            refine ⟨567349212640751602069283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378232808427167734712855 567349212640751602069283)
            ·
              refine ⟨851023818961127403103925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567349212640751602069283 851023818961127403103925)
              ·
                refine ⟨79783483027605694040993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 851023818961127403103925 79783483027605694040993)
                ·
                  refine ⟨59837612270704270530745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79783483027605694040993 59837612270704270530745)
                  ·
                    rfl

theorem cell20_131100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_131100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131100 prefixEnd_131100 := by exact prefixLift 131100
  have htrace : WordTrace (prefixWord ++ tailWord_131100) baseStart_131100 baseEnd_131100 := by
    simpa [prefixWord, tailWord_131100, baseEnd_131100] using wordTrace_append hprefix tailTrace_131100
  have hstable : (prefixWord ++ tailWord_131100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131100).length < 2 ^ (prefixWord ++ tailWord_131100).sum := by decide
  have hdescent : baseEnd_131100 < baseStart_131100 := by decide
  rcases family_descends (prefixWord ++ tailWord_131100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131114 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_131114 : Nat := 118140960795 + 131114 * 2 ^ 59
def prefixEnd_131114 : Nat := 4983230072969 + 3 ^ 40 * 131114 * 2
def baseEnd_131114 : Nat := 59844002252182444064021

theorem tailTrace_131114 : CollatzResearch.WordTrace tailWord_131114 prefixEnd_131114 59844002252182444064021 := by
  unfold tailWord_131114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195530111750961333388099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3188080298002563555701597 1195530111750961333388099)
  ·
    refine ⟨1793295167626442000082149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1195530111750961333388099 1793295167626442000082149)
    ·
      refine ⟨336242843929957875015403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1793295167626442000082149 336242843929957875015403)
      ·
        refine ⟨504364265894936812523105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336242843929957875015403 504364265894936812523105)
        ·
          refine ⟨378273199421202609392329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504364265894936812523105 378273199421202609392329)
          ·
            refine ⟨283704899565901957044247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378273199421202609392329 283704899565901957044247)
            ·
              refine ⟨425557349348852935566371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283704899565901957044247 425557349348852935566371)
              ·
                refine ⟨638336024023279403349557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425557349348852935566371 638336024023279403349557)
                ·
                  refine ⟨59844002252182444064021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 638336024023279403349557 59844002252182444064021)
                  ·
                    rfl

theorem cell20_131114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_131114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131114 prefixEnd_131114 := by exact prefixLift 131114
  have htrace : WordTrace (prefixWord ++ tailWord_131114) baseStart_131114 baseEnd_131114 := by
    simpa [prefixWord, tailWord_131114, baseEnd_131114] using wordTrace_append hprefix tailTrace_131114
  have hstable : (prefixWord ++ tailWord_131114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131114).length < 2 ^ (prefixWord ++ tailWord_131114).sum := by decide
  have hdescent : baseEnd_131114 < baseStart_131114 := by decide
  rcases family_descends (prefixWord ++ tailWord_131114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131121 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_131121 : Nat := 118140960795 + 131121 * 2 ^ 59
def prefixEnd_131121 : Nat := 4983230072969 + 3 ^ 40 * 131121 * 2
def baseEnd_131121 : Nat := 59847197242921530830659

theorem tailTrace_131121 : CollatzResearch.WordTrace tailWord_131121 prefixEnd_131121 59847197242921530830659 := by
  unfold tailWord_131121
  simp only [CollatzResearch.WordTrace]
  refine ⟨4782375757978485529057217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3188250505318990352704811 4782375757978485529057217)
  ·
    refine ⟨3586781818483864146792913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4782375757978485529057217 3586781818483864146792913)
    ·
      refine ⟨2690086363862898110094685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3586781818483864146792913 2690086363862898110094685)
      ·
        refine ⟨1008782386448586791285507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2690086363862898110094685 1008782386448586791285507)
        ·
          refine ⟨1513173579672880186928261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008782386448586791285507 1513173579672880186928261)
          ·
            refine ⟨283720046188665035049049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1513173579672880186928261 283720046188665035049049)
            ·
              refine ⟨212790034641498776286787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283720046188665035049049 212790034641498776286787)
              ·
                refine ⟨319185051962248164430181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212790034641498776286787 319185051962248164430181)
                ·
                  refine ⟨59847197242921530830659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319185051962248164430181 59847197242921530830659)
                  ·
                    rfl

theorem cell20_131121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_131121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131121 prefixEnd_131121 := by exact prefixLift 131121
  have htrace : WordTrace (prefixWord ++ tailWord_131121) baseStart_131121 baseEnd_131121 := by
    simpa [prefixWord, tailWord_131121, baseEnd_131121] using wordTrace_append hprefix tailTrace_131121
  have hstable : (prefixWord ++ tailWord_131121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131121).length < 2 ^ (prefixWord ++ tailWord_131121).sum := by decide
  have hdescent : baseEnd_131121 < baseStart_131121 := by decide
  rcases family_descends (prefixWord ++ tailWord_131121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131135 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 3]
def baseStart_131135 : Nat := 118140960795 + 131135 * 2 ^ 59
def prefixEnd_131135 : Nat := 4983230072969 + 3 ^ 40 * 131135 * 2
def baseEnd_131135 : Nat := 59853587224399704363935

theorem tailTrace_131135 : CollatzResearch.WordTrace tailWord_131135 prefixEnd_131135 59853587224399704363935 := by
  unfold tailWord_131135
  simp only [CollatzResearch.WordTrace]
  refine ⟨4782886379927765920066859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3188590919951843946711239 4782886379927765920066859)
  ·
    refine ⟨7174329569891648880100289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4782886379927765920066859 7174329569891648880100289)
    ·
      refine ⟨5380747177418736660075217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7174329569891648880100289 5380747177418736660075217)
      ·
        refine ⟨4035560383064052495056413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5380747177418736660075217 4035560383064052495056413)
        ·
          refine ⟨1513335143649019685646155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4035560383064052495056413 1513335143649019685646155)
          ·
            refine ⟨2270002715473529528469233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513335143649019685646155 2270002715473529528469233)
            ·
              refine ⟨1702502036605147146351925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2270002715473529528469233 1702502036605147146351925)
              ·
                refine ⟨159609565931732544970493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1702502036605147146351925 159609565931732544970493)
                ·
                  refine ⟨59853587224399704363935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159609565931732544970493 59853587224399704363935)
                  ·
                    rfl

theorem cell20_131135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_131135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131135 prefixEnd_131135 := by exact prefixLift 131135
  have htrace : WordTrace (prefixWord ++ tailWord_131135) baseStart_131135 baseEnd_131135 := by
    simpa [prefixWord, tailWord_131135, baseEnd_131135] using wordTrace_append hprefix tailTrace_131135
  have hstable : (prefixWord ++ tailWord_131135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131135).length < 2 ^ (prefixWord ++ tailWord_131135).sum := by decide
  have hdescent : baseEnd_131135 < baseStart_131135 := by decide
  rcases family_descends (prefixWord ++ tailWord_131135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131173 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_131173 : Nat := 118140960795 + 131173 * 2 ^ 59
def prefixEnd_131173 : Nat := 4983230072969 + 3 ^ 40 * 131173 * 2
def baseEnd_131173 : Nat := 59870931459840461097113

theorem tailTrace_131173 : CollatzResearch.WordTrace tailWord_131173 prefixEnd_131173 59870931459840461097113 := by
  unfold tailWord_131173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4784272353790098409950173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3189514902526732273300115 4784272353790098409950173)
  ·
    refine ⟨1794102132671286903731315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4784272353790098409950173 1794102132671286903731315)
    ·
      refine ⟨2691153199006930355596973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794102132671286903731315 2691153199006930355596973)
      ·
        refine ⟨1009182449627598883348865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2691153199006930355596973 1009182449627598883348865)
        ·
          refine ⟨756886837220699162511649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009182449627598883348865 756886837220699162511649)
          ·
            refine ⟨567665127915524371883737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756886837220699162511649 567665127915524371883737)
            ·
              refine ⟨425748845936643278912803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567665127915524371883737 425748845936643278912803)
              ·
                refine ⟨638623268904964918369205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425748845936643278912803 638623268904964918369205)
                ·
                  refine ⟨59870931459840461097113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 638623268904964918369205 59870931459840461097113)
                  ·
                    rfl

theorem cell20_131173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_131173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131173 prefixEnd_131173 := by exact prefixLift 131173
  have htrace : WordTrace (prefixWord ++ tailWord_131173) baseStart_131173 baseEnd_131173 := by
    simpa [prefixWord, tailWord_131173, baseEnd_131173] using wordTrace_append hprefix tailTrace_131173
  have hstable : (prefixWord ++ tailWord_131173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131173).length < 2 ^ (prefixWord ++ tailWord_131173).sum := by decide
  have hdescent : baseEnd_131173 < baseStart_131173 := by decide
  rcases family_descends (prefixWord ++ tailWord_131173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131228 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_131228 : Nat := 118140960795 + 131228 * 2 ^ 59
def prefixEnd_131228 : Nat := 4983230072969 + 3 ^ 40 * 131228 * 2
def baseEnd_131228 : Nat := 59896034958504714263555

theorem tailTrace_131228 : CollatzResearch.WordTrace tailWord_131228 prefixEnd_131228 59896034958504714263555 := by
  unfold tailWord_131228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393139184295421401601169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3190852245727228535468225 2393139184295421401601169)
  ·
    refine ⟨1794854388221566051200877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2393139184295421401601169 1794854388221566051200877)
    ·
      refine ⟨673070395583087269200329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1794854388221566051200877 673070395583087269200329)
      ·
        refine ⟨504802796687315451900247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673070395583087269200329 504802796687315451900247)
        ·
          refine ⟨757204195030973177850371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504802796687315451900247 757204195030973177850371)
          ·
            refine ⟨1135806292546459766775557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757204195030973177850371 1135806292546459766775557)
            ·
              refine ⟨212963679852461206270417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1135806292546459766775557 212963679852461206270417)
              ·
                refine ⟨159722759889345904702813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212963679852461206270417 159722759889345904702813)
                ·
                  refine ⟨59896034958504714263555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159722759889345904702813 59896034958504714263555)
                  ·
                    rfl

theorem cell20_131228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_131228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131228 prefixEnd_131228 := by exact prefixLift 131228
  have htrace : WordTrace (prefixWord ++ tailWord_131228) baseStart_131228 baseEnd_131228 := by
    simpa [prefixWord, tailWord_131228, baseEnd_131228] using wordTrace_append hprefix tailTrace_131228
  have hstable : (prefixWord ++ tailWord_131228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131228).length < 2 ^ (prefixWord ++ tailWord_131228).sum := by decide
  have hdescent : baseEnd_131228 < baseStart_131228 := by decide
  rcases family_descends (prefixWord ++ tailWord_131228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131231 : List Nat := [1, 1, 2, 6, 1, 1, 4, 2, 2]
def baseStart_131231 : Nat := 118140960795 + 131231 * 2 ^ 59
def prefixEnd_131231 : Nat := 4983230072969 + 3 ^ 40 * 131231 * 2
def baseEnd_131231 : Nat := 59897404240250037163543

theorem tailTrace_131231 : CollatzResearch.WordTrace tailWord_131231 prefixEnd_131231 59897404240250037163543 := by
  unfold tailWord_131231
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786387787579974315561547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3190925191719982877041031 4786387787579974315561547)
  ·
    refine ⟨7179581681369961473342321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4786387787579974315561547 7179581681369961473342321)
    ·
      refine ⟨5384686261027471105006741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7179581681369961473342321 5384686261027471105006741)
      ·
        refine ⟨252407168485662708047191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5384686261027471105006741 252407168485662708047191)
        ·
          refine ⟨378610752728494062070787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252407168485662708047191 378610752728494062070787)
          ·
            refine ⟨567916129092741093106181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378610752728494062070787 567916129092741093106181)
            ·
              refine ⟨106484274204888954957409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 567916129092741093106181 106484274204888954957409)
              ·
                refine ⟨79863205653666716218057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106484274204888954957409 79863205653666716218057)
                ·
                  refine ⟨59897404240250037163543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79863205653666716218057 59897404240250037163543)
                  ·
                    rfl

theorem cell20_131231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 2].length) (baseStart_131231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131231 prefixEnd_131231 := by exact prefixLift 131231
  have htrace : WordTrace (prefixWord ++ tailWord_131231) baseStart_131231 baseEnd_131231 := by
    simpa [prefixWord, tailWord_131231, baseEnd_131231] using wordTrace_append hprefix tailTrace_131231
  have hstable : (prefixWord ++ tailWord_131231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131231).length < 2 ^ (prefixWord ++ tailWord_131231).sum := by decide
  have hdescent : baseEnd_131231 < baseStart_131231 := by decide
  rcases family_descends (prefixWord ++ tailWord_131231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131256 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_131256 : Nat := 118140960795 + 131256 * 2 ^ 59
def prefixEnd_131256 : Nat := 4983230072969 + 3 ^ 40 * 131256 * 2
def baseEnd_131256 : Nat := 59908814921461061330107

theorem tailTrace_131256 : CollatzResearch.WordTrace tailWord_131256 prefixEnd_131256 59908814921461061330107 := by
  unfold tailWord_131256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393649806244701792610811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3191533074992935723481081 2393649806244701792610811)
  ·
    refine ⟨3590474709367052688916217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393649806244701792610811 3590474709367052688916217)
    ·
      refine ⟨2692856032025289516687163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3590474709367052688916217 2692856032025289516687163)
      ·
        refine ⟨4039284048037934275030745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2692856032025289516687163 4039284048037934275030745)
        ·
          refine ⟨3029463036028450706273059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4039284048037934275030745 3029463036028450706273059)
          ·
            refine ⟨4544194554042676059409589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3029463036028450706273059 4544194554042676059409589)
            ·
              refine ⟨426018239441500880569649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4544194554042676059409589 426018239441500880569649)
              ·
                refine ⟨319513679581125660427237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426018239441500880569649 319513679581125660427237)
                ·
                  refine ⟨59908814921461061330107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319513679581125660427237 59908814921461061330107)
                  ·
                    rfl

theorem cell20_131256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_131256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131256 prefixEnd_131256 := by exact prefixLift 131256
  have htrace : WordTrace (prefixWord ++ tailWord_131256) baseStart_131256 baseEnd_131256 := by
    simpa [prefixWord, tailWord_131256, baseEnd_131256] using wordTrace_append hprefix tailTrace_131256
  have hstable : (prefixWord ++ tailWord_131256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131256).length < 2 ^ (prefixWord ++ tailWord_131256).sum := by decide
  have hdescent : baseEnd_131256 < baseStart_131256 := by decide
  rcases family_descends (prefixWord ++ tailWord_131256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131335 : List Nat := [1, 1, 4, 5, 1, 2, 6]
def baseStart_131335 : Nat := 118140960795 + 131335 * 2 ^ 59
def prefixEnd_131335 : Nat := 4983230072969 + 3 ^ 40 * 131335 * 2
def baseEnd_131335 : Nat := 6660541408231988632939

theorem tailTrace_131335 : CollatzResearch.WordTrace tailWord_131335 prefixEnd_131335 6660541408231988632939 := by
  unfold tailWord_131335
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790180979203200077347459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3193453986135466718231639 4790180979203200077347459)
  ·
    refine ⟨7185271468804800116021189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4790180979203200077347459 7185271468804800116021189)
    ·
      refine ⟨1347238400400900021753973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7185271468804800116021189 1347238400400900021753973)
      ·
        refine ⟨126303600037584377039435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1347238400400900021753973 126303600037584377039435)
        ·
          refine ⟨189455400056376565559153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126303600037584377039435 189455400056376565559153)
          ·
            refine ⟨142091550042282424169365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189455400056376565559153 142091550042282424169365)
            ·
              refine ⟨6660541408231988632939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142091550042282424169365 6660541408231988632939)
              ·
                rfl

theorem cell20_131335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 6].length) (baseStart_131335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131335 prefixEnd_131335 := by exact prefixLift 131335
  have htrace : WordTrace (prefixWord ++ tailWord_131335) baseStart_131335 baseEnd_131335 := by
    simpa [prefixWord, tailWord_131335, baseEnd_131335] using wordTrace_append hprefix tailTrace_131335
  have hstable : (prefixWord ++ tailWord_131335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131335).length < 2 ^ (prefixWord ++ tailWord_131335).sum := by decide
  have hdescent : baseEnd_131335 < baseStart_131335 := by decide
  rcases family_descends (prefixWord ++ tailWord_131335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131349 : List Nat := [1, 3, 2, 1, 2, 1, 2, 6, 2]
def baseStart_131349 : Nat := 118140960795 + 131349 * 2 ^ 59
def prefixEnd_131349 : Nat := 4983230072969 + 3 ^ 40 * 131349 * 2
def baseEnd_131349 : Nat := 59951262655566071229727

theorem tailTrace_131349 : CollatzResearch.WordTrace tailWord_131349 prefixEnd_131349 59951262655566071229727 := by
  unfold tailWord_131349
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790691601152480468357101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3193794400768320312238067 4790691601152480468357101)
  ·
    refine ⟨1796509350432180175633913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4790691601152480468357101 1796509350432180175633913)
    ·
      refine ⟨1347382012824135131725435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1796509350432180175633913 1347382012824135131725435)
      ·
        refine ⟨2021073019236202697588153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1347382012824135131725435 2021073019236202697588153)
        ·
          refine ⟨1515804764427152023191115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2021073019236202697588153 1515804764427152023191115)
          ·
            refine ⟨2273707146640728034786673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515804764427152023191115 2273707146640728034786673)
            ·
              refine ⟨1705280359980546026090005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2273707146640728034786673 1705280359980546026090005)
              ·
                refine ⟨79935016874088094972969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1705280359980546026090005 79935016874088094972969)
                ·
                  refine ⟨59951262655566071229727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79935016874088094972969 59951262655566071229727)
                  ·
                    rfl

theorem cell20_131349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_131349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131349 prefixEnd_131349 := by exact prefixLift 131349
  have htrace : WordTrace (prefixWord ++ tailWord_131349) baseStart_131349 baseEnd_131349 := by
    simpa [prefixWord, tailWord_131349, baseEnd_131349] using wordTrace_append hprefix tailTrace_131349
  have hstable : (prefixWord ++ tailWord_131349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131349).length < 2 ^ (prefixWord ++ tailWord_131349).sum := by decide
  have hdescent : baseEnd_131349 < baseStart_131349 := by decide
  rcases family_descends (prefixWord ++ tailWord_131349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131359 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 3]
def baseStart_131359 : Nat := 118140960795 + 131359 * 2 ^ 59
def prefixEnd_131359 : Nat := 4983230072969 + 3 ^ 40 * 131359 * 2
def baseEnd_131359 : Nat := 59955826928050480896353

theorem tailTrace_131359 : CollatzResearch.WordTrace tailWord_131359 prefixEnd_131359 59955826928050480896353 := by
  unfold tailWord_131359
  simp only [CollatzResearch.WordTrace]
  refine ⟨4791056331116252176221131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3194037554077501450814087 4791056331116252176221131)
  ·
    refine ⟨7186584496674378264331697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4791056331116252176221131 7186584496674378264331697)
    ·
      refine ⟨5389938372505783698248773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7186584496674378264331697 5389938372505783698248773)
      ·
        refine ⟨1010613444844834443421645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5389938372505783698248773 1010613444844834443421645)
        ·
          refine ⟨378980041816812916283117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1010613444844834443421645 378980041816812916283117)
          ·
            refine ⟨142117515681304843606169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378980041816812916283117 142117515681304843606169)
            ·
              refine ⟨106588136760978632704627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142117515681304843606169 106588136760978632704627)
              ·
                refine ⟨159882205141467949056941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106588136760978632704627 159882205141467949056941)
                ·
                  refine ⟨59955826928050480896353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159882205141467949056941 59955826928050480896353)
                  ·
                    rfl

theorem cell20_131359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 3].length) (baseStart_131359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131359 prefixEnd_131359 := by exact prefixLift 131359
  have htrace : WordTrace (prefixWord ++ tailWord_131359) baseStart_131359 baseEnd_131359 := by
    simpa [prefixWord, tailWord_131359, baseEnd_131359] using wordTrace_append hprefix tailTrace_131359
  have hstable : (prefixWord ++ tailWord_131359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131359).length < 2 ^ (prefixWord ++ tailWord_131359).sum := by decide
  have hdescent : baseEnd_131359 < baseStart_131359 := by decide
  rcases family_descends (prefixWord ++ tailWord_131359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131363 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 3]
def baseStart_131363 : Nat := 118140960795 + 131363 * 2 ^ 59
def prefixEnd_131363 : Nat := 4983230072969 + 3 ^ 40 * 131363 * 2
def baseEnd_131363 : Nat := 59957652637044244763003

theorem tailTrace_131363 : CollatzResearch.WordTrace tailWord_131363 prefixEnd_131363 59957652637044244763003 := by
  unfold tailWord_131363
  simp only [CollatzResearch.WordTrace]
  refine ⟨4791202223101760859366743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3194134815401173906244495 4791202223101760859366743)
  ·
    refine ⟨7186803334652641289050115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4791202223101760859366743 7186803334652641289050115)
    ·
      refine ⟨10780205001978961933575173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7186803334652641289050115 10780205001978961933575173)
      ·
        refine ⟨2021288437871055362545345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10780205001978961933575173 2021288437871055362545345)
        ·
          refine ⟨1515966328403291521909009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2021288437871055362545345 1515966328403291521909009)
          ·
            refine ⟨1136974746302468641431757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515966328403291521909009 1136974746302468641431757)
            ·
              refine ⟨426365529863425740536909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1136974746302468641431757 426365529863425740536909)
              ·
                refine ⟨159887073698784652701341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426365529863425740536909 159887073698784652701341)
                ·
                  refine ⟨59957652637044244763003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159887073698784652701341 59957652637044244763003)
                  ·
                    rfl

theorem cell20_131363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_131363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131363 prefixEnd_131363 := by exact prefixLift 131363
  have htrace : WordTrace (prefixWord ++ tailWord_131363) baseStart_131363 baseEnd_131363 := by
    simpa [prefixWord, tailWord_131363, baseEnd_131363] using wordTrace_append hprefix tailTrace_131363
  have hstable : (prefixWord ++ tailWord_131363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131363).length < 2 ^ (prefixWord ++ tailWord_131363).sum := by decide
  have hdescent : baseEnd_131363 < baseStart_131363 := by decide
  rcases family_descends (prefixWord ++ tailWord_131363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131384 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_131384 : Nat := 118140960795 + 131384 * 2 ^ 59
def prefixEnd_131384 : Nat := 4983230072969 + 3 ^ 40 * 131384 * 2
def baseEnd_131384 : Nat := 59967237609261505062917

theorem tailTrace_131384 : CollatzResearch.WordTrace tailWord_131384 prefixEnd_131384 59967237609261505062917 := by
  unfold tailWord_131384
  simp only [CollatzResearch.WordTrace]
  refine ⟨2395984078012840722940603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3194645437350454297254137 2395984078012840722940603)
  ·
    refine ⟨3593976117019261084410905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2395984078012840722940603 3593976117019261084410905)
    ·
      refine ⟨2695482087764445813308179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3593976117019261084410905 2695482087764445813308179)
      ·
        refine ⟨4043223131646668719962269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2695482087764445813308179 4043223131646668719962269)
        ·
          refine ⟨1516208674367500769985851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4043223131646668719962269 1516208674367500769985851)
          ·
            refine ⟨2274313011551251154978777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516208674367500769985851 2274313011551251154978777)
            ·
              refine ⟨1705734758663438366234083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2274313011551251154978777 1705734758663438366234083)
              ·
                refine ⟨2558602137995157549351125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1705734758663438366234083 2558602137995157549351125)
                ·
                  refine ⟨59967237609261505062917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2558602137995157549351125 59967237609261505062917)
                  ·
                    rfl

theorem cell20_131384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_131384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131384 prefixEnd_131384 := by exact prefixLift 131384
  have htrace : WordTrace (prefixWord ++ tailWord_131384) baseStart_131384 baseEnd_131384 := by
    simpa [prefixWord, tailWord_131384, baseEnd_131384] using wordTrace_append hprefix tailTrace_131384
  have hstable : (prefixWord ++ tailWord_131384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131384).length < 2 ^ (prefixWord ++ tailWord_131384).sum := by decide
  have hdescent : baseEnd_131384 < baseStart_131384 := by decide
  rcases family_descends (prefixWord ++ tailWord_131384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131442 : List Nat := [3, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_131442 : Nat := 118140960795 + 131442 * 2 ^ 59
def prefixEnd_131442 : Nat := 4983230072969 + 3 ^ 40 * 131442 * 2
def baseEnd_131442 : Nat := 59993710389671081129347

theorem tailTrace_131442 : CollatzResearch.WordTrace tailWord_131442 prefixEnd_131442 59993710389671081129347 := by
  unfold tailWord_131442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198520897453889337873145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3196055726543704900995053 1198520897453889337873145)
  ·
    refine ⟨898890673090417003404859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1198520897453889337873145 898890673090417003404859)
    ·
      refine ⟨1348336009635625505107289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 898890673090417003404859 1348336009635625505107289)
      ·
        refine ⟨1011252007226719128830467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1348336009635625505107289 1011252007226719128830467)
        ·
          refine ⟨1516878010840078693245701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011252007226719128830467 1516878010840078693245701)
          ·
            refine ⟨284414627032514754983569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1516878010840078693245701 284414627032514754983569)
            ·
              refine ⟨213310970274386066237677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284414627032514754983569 213310970274386066237677)
              ·
                refine ⟨79991613852894774839129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213310970274386066237677 79991613852894774839129)
                ·
                  refine ⟨59993710389671081129347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79991613852894774839129 59993710389671081129347)
                  ·
                    rfl

theorem cell20_131442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_131442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131442 prefixEnd_131442 := by exact prefixLift 131442
  have htrace : WordTrace (prefixWord ++ tailWord_131442) baseStart_131442 baseEnd_131442 := by
    simpa [prefixWord, tailWord_131442, baseEnd_131442] using wordTrace_append hprefix tailTrace_131442
  have hstable : (prefixWord ++ tailWord_131442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131442).length < 2 ^ (prefixWord ++ tailWord_131442).sum := by decide
  have hdescent : baseEnd_131442 < baseStart_131442 := by decide
  rcases family_descends (prefixWord ++ tailWord_131442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131453 : List Nat := [1, 4, 1, 1, 2, 4, 7]
def baseStart_131453 : Nat := 118140960795 + 131453 * 2 ^ 59
def prefixEnd_131453 : Nat := 4983230072969 + 3 ^ 40 * 131453 * 2
def baseEnd_131453 : Nat := 6666525676600436862515

theorem tailTrace_131453 : CollatzResearch.WordTrace tailWord_131453 prefixEnd_131453 6666525676600436862515 := by
  unfold tailWord_131453
  simp only [CollatzResearch.WordTrace]
  refine ⟨4794484792775706230143013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3196323195183804153428675 4794484792775706230143013)
  ·
    refine ⟨898965898645444918151815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4794484792775706230143013 898965898645444918151815)
    ·
      refine ⟨1348448847968167377227723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 898965898645444918151815 1348448847968167377227723)
      ·
        refine ⟨2022673271952251065841585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348448847968167377227723 2022673271952251065841585)
        ·
          refine ⟨1517004953964188299381189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022673271952251065841585 1517004953964188299381189)
          ·
            refine ⟨284438428868285306133973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1517004953964188299381189 284438428868285306133973)
            ·
              refine ⟨6666525676600436862515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 284438428868285306133973 6666525676600436862515)
              ·
                rfl

theorem cell20_131453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 7].length) (baseStart_131453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131453 prefixEnd_131453 := by exact prefixLift 131453
  have htrace : WordTrace (prefixWord ++ tailWord_131453) baseStart_131453 baseEnd_131453 := by
    simpa [prefixWord, tailWord_131453, baseEnd_131453] using wordTrace_append hprefix tailTrace_131453
  have hstable : (prefixWord ++ tailWord_131453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131453).length < 2 ^ (prefixWord ++ tailWord_131453).sum := by decide
  have hdescent : baseEnd_131453 < baseStart_131453 := by decide
  rcases family_descends (prefixWord ++ tailWord_131453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131463 : List Nat := [1, 1, 4, 2, 2, 1, 1, 6, 2]
def baseStart_131463 : Nat := 118140960795 + 131463 * 2 ^ 59
def prefixEnd_131463 : Nat := 4983230072969 + 3 ^ 40 * 131463 * 2
def baseEnd_131463 : Nat := 60003295361888341429261

theorem tailTrace_131463 : CollatzResearch.WordTrace tailWord_131463 prefixEnd_131463 60003295361888341429261 := by
  unfold tailWord_131463
  simp only [CollatzResearch.WordTrace]
  refine ⟨4794849522739477938007043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3196566348492985292004695 4794849522739477938007043)
  ·
    refine ⟨7192274284109216907010565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4794849522739477938007043 7192274284109216907010565)
    ·
      refine ⟨1348551428270478170064481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7192274284109216907010565 1348551428270478170064481)
      ·
        refine ⟨1011413571202858627548361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1348551428270478170064481 1011413571202858627548361)
        ·
          refine ⟨758560178402143970661271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1011413571202858627548361 758560178402143970661271)
          ·
            refine ⟨1137840267603215955991907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758560178402143970661271 1137840267603215955991907)
            ·
              refine ⟨1706760401404823933987861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137840267603215955991907 1706760401404823933987861)
              ·
                refine ⟨80004393815851121905681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1706760401404823933987861 80004393815851121905681)
                ·
                  refine ⟨60003295361888341429261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80004393815851121905681 60003295361888341429261)
                  ·
                    rfl

theorem cell20_131463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 2].length) (baseStart_131463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131463 prefixEnd_131463 := by exact prefixLift 131463
  have htrace : WordTrace (prefixWord ++ tailWord_131463) baseStart_131463 baseEnd_131463 := by
    simpa [prefixWord, tailWord_131463, baseEnd_131463] using wordTrace_append hprefix tailTrace_131463
  have hstable : (prefixWord ++ tailWord_131463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131463).length < 2 ^ (prefixWord ++ tailWord_131463).sum := by decide
  have hdescent : baseEnd_131463 < baseStart_131463 := by decide
  rcases family_descends (prefixWord ++ tailWord_131463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131491 : List Nat := [1, 1, 1, 4, 1, 5, 1, 6]
def baseStart_131491 : Nat := 118140960795 + 131491 * 2 ^ 59
def prefixEnd_131491 : Nat := 4983230072969 + 3 ^ 40 * 131491 * 2
def baseEnd_131491 : Nat := 20005358441614896165271

theorem tailTrace_131491 : CollatzResearch.WordTrace tailWord_131491 prefixEnd_131491 20005358441614896165271 := by
  unfold tailWord_131491
  simp only [CollatzResearch.WordTrace]
  refine ⟨4795870766638038720026327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3197247177758692480017551 4795870766638038720026327)
  ·
    refine ⟨7193806149957058080039491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4795870766638038720026327 7193806149957058080039491)
    ·
      refine ⟨10790709224935587120059237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7193806149957058080039491 10790709224935587120059237)
      ·
        refine ⟨2023257979675422585011107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10790709224935587120059237 2023257979675422585011107)
        ·
          refine ⟨3034886969513133877516661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023257979675422585011107 3034886969513133877516661)
          ·
            refine ⟨284520653391856301017187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3034886969513133877516661 284520653391856301017187)
            ·
              refine ⟨426780980087784451525781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284520653391856301017187 426780980087784451525781)
              ·
                refine ⟨20005358441614896165271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 426780980087784451525781 20005358441614896165271)
                ·
                  rfl

theorem cell20_131491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_131491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131491 prefixEnd_131491 := by exact prefixLift 131491
  have htrace : WordTrace (prefixWord ++ tailWord_131491) baseStart_131491 baseEnd_131491 := by
    simpa [prefixWord, tailWord_131491, baseEnd_131491] using wordTrace_append hprefix tailTrace_131491
  have hstable : (prefixWord ++ tailWord_131491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131491).length < 2 ^ (prefixWord ++ tailWord_131491).sum := by decide
  have hdescent : baseEnd_131491 < baseStart_131491 := by decide
  rcases family_descends (prefixWord ++ tailWord_131491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131532 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 3]
def baseStart_131532 : Nat := 118140960795 + 131532 * 2 ^ 59
def prefixEnd_131532 : Nat := 4983230072969 + 3 ^ 40 * 131532 * 2
def baseEnd_131532 : Nat := 60034788842030768128979

theorem tailTrace_131532 : CollatzResearch.WordTrace tailWord_131532 prefixEnd_131532 60034788842030768128979 := by
  unfold tailWord_131532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398683079744751361134425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3198244106326335148179233 2398683079744751361134425)
  ·
    refine ⟨1799012309808563520850819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2398683079744751361134425 1799012309808563520850819)
    ·
      refine ⟨2698518464712845281276229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1799012309808563520850819 2698518464712845281276229)
      ·
        refine ⟨505972212133658490239293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2698518464712845281276229 505972212133658490239293)
        ·
          refine ⟨189739579550121933839735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505972212133658490239293 189739579550121933839735)
          ·
            refine ⟨284609369325182900759603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189739579550121933839735 284609369325182900759603)
            ·
              refine ⟨426914053987774351139405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284609369325182900759603 426914053987774351139405)
              ·
                refine ⟨160092770245415381677277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426914053987774351139405 160092770245415381677277)
                ·
                  refine ⟨60034788842030768128979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160092770245415381677277 60034788842030768128979)
                  ·
                    rfl

theorem cell20_131532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_131532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131532 prefixEnd_131532 := by exact prefixLift 131532
  have htrace : WordTrace (prefixWord ++ tailWord_131532) baseStart_131532 baseEnd_131532 := by
    simpa [prefixWord, tailWord_131532, baseEnd_131532] using wordTrace_append hprefix tailTrace_131532
  have hstable : (prefixWord ++ tailWord_131532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131532).length < 2 ^ (prefixWord ++ tailWord_131532).sum := by decide
  have hdescent : baseEnd_131532 < baseStart_131532 := by decide
  rcases family_descends (prefixWord ++ tailWord_131532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131573 : List Nat := [1, 3, 5, 1, 2, 1, 1, 4, 2]
def baseStart_131573 : Nat := 118140960795 + 131573 * 2 ^ 59
def prefixEnd_131573 : Nat := 4983230072969 + 3 ^ 40 * 131573 * 2
def baseEnd_131573 : Nat := 60053502359216847762145

theorem tailTrace_131573 : CollatzResearch.WordTrace tailWord_131573 prefixEnd_131573 60053502359216847762145 := by
  unfold tailWord_131573
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798861552340966724511373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3199241034893977816340915 4798861552340966724511373)
  ·
    refine ⟨1799573082127862521691765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4798861552340966724511373 1799573082127862521691765)
    ·
      refine ⟨168709976449487111408603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1799573082127862521691765 168709976449487111408603)
      ·
        refine ⟨253064964674230667112905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168709976449487111408603 253064964674230667112905)
        ·
          refine ⟨189798723505673000334679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253064964674230667112905 189798723505673000334679)
          ·
            refine ⟨284698085258509500502019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189798723505673000334679 284698085258509500502019)
            ·
              refine ⟨427047127887764250753029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284698085258509500502019 427047127887764250753029)
              ·
                refine ⟨80071336478955797016193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 427047127887764250753029 80071336478955797016193)
                ·
                  refine ⟨60053502359216847762145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80071336478955797016193 60053502359216847762145)
                  ·
                    rfl

theorem cell20_131573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_131573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131573 prefixEnd_131573 := by exact prefixLift 131573
  have htrace : WordTrace (prefixWord ++ tailWord_131573) baseStart_131573 baseEnd_131573 := by
    simpa [prefixWord, tailWord_131573, baseEnd_131573] using wordTrace_append hprefix tailTrace_131573
  have hstable : (prefixWord ++ tailWord_131573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131573).length < 2 ^ (prefixWord ++ tailWord_131573).sum := by decide
  have hdescent : baseEnd_131573 < baseStart_131573 := by decide
  rcases family_descends (prefixWord ++ tailWord_131573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131598 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_131598 : Nat := 118140960795 + 131598 * 2 ^ 59
def prefixEnd_131598 : Nat := 4983230072969 + 3 ^ 40 * 131598 * 2
def baseEnd_131598 : Nat := 60064913040427871928709

theorem tailTrace_131598 : CollatzResearch.WordTrace tailWord_131598 prefixEnd_131598 60064913040427871928709 := by
  unfold tailWord_131598
  simp only [CollatzResearch.WordTrace]
  refine ⟨599971672156299499271431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3199848918166930662780965 599971672156299499271431)
  ·
    refine ⟨899957508234449248907147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 599971672156299499271431 899957508234449248907147)
    ·
      refine ⟨1349936262351673873360721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899957508234449248907147 1349936262351673873360721)
      ·
        refine ⟨1012452196763755405020541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1349936262351673873360721 1012452196763755405020541)
        ·
          refine ⟨379669573786408276882703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1012452196763755405020541 379669573786408276882703)
          ·
            refine ⟨569504360679612415324055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379669573786408276882703 569504360679612415324055)
            ·
              refine ⟨854256541019418622986083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569504360679612415324055 854256541019418622986083)
              ·
                refine ⟨1281384811529127934479125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854256541019418622986083 1281384811529127934479125)
                ·
                  refine ⟨60064913040427871928709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1281384811529127934479125 60064913040427871928709)
                  ·
                    rfl

theorem cell20_131598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_131598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131598 prefixEnd_131598 := by exact prefixLift 131598
  have htrace : WordTrace (prefixWord ++ tailWord_131598) baseStart_131598 baseEnd_131598 := by
    simpa [prefixWord, tailWord_131598, baseEnd_131598] using wordTrace_append hprefix tailTrace_131598
  have hstable : (prefixWord ++ tailWord_131598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131598).length < 2 ^ (prefixWord ++ tailWord_131598).sum := by decide
  have hdescent : baseEnd_131598 < baseStart_131598 := by decide
  rcases family_descends (prefixWord ++ tailWord_131598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131652 : List Nat := [2, 3, 5, 1, 2, 1, 2, 4]
def baseStart_131652 : Nat := 118140960795 + 131652 * 2 ^ 59
def prefixEnd_131652 : Nat := 4983230072969 + 3 ^ 40 * 131652 * 2
def baseEnd_131652 : Nat := 20029853370614561376163

theorem tailTrace_131652 : CollatzResearch.WordTrace tailWord_131652 prefixEnd_131652 20029853370614561376163 := by
  unfold tailWord_131652
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400871459527381608318605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3201161946036508811091473 2400871459527381608318605)
  ·
    refine ⟨900326797322768103119477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2400871459527381608318605 900326797322768103119477)
    ·
      refine ⟨84405637249009509667451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 900326797322768103119477 84405637249009509667451)
      ·
        refine ⟨126608455873514264501177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84405637249009509667451 126608455873514264501177)
        ·
          refine ⟨94956341905135698375883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126608455873514264501177 94956341905135698375883)
          ·
            refine ⟨142434512857703547563825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94956341905135698375883 142434512857703547563825)
            ·
              refine ⟨106825884643277660672869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142434512857703547563825 106825884643277660672869)
              ·
                refine ⟨20029853370614561376163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106825884643277660672869 20029853370614561376163)
                ·
                  rfl

theorem cell20_131652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_131652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131652 prefixEnd_131652 := by exact prefixLift 131652
  have htrace : WordTrace (prefixWord ++ tailWord_131652) baseStart_131652 baseEnd_131652 := by
    simpa [prefixWord, tailWord_131652, baseEnd_131652] using wordTrace_append hprefix tailTrace_131652
  have hstable : (prefixWord ++ tailWord_131652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131652).length < 2 ^ (prefixWord ++ tailWord_131652).sum := by decide
  have hdescent : baseEnd_131652 < baseStart_131652 := by decide
  rcases family_descends (prefixWord ++ tailWord_131652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131681 : List Nat := [1, 2, 3, 1, 1, 6, 6]
def baseStart_131681 : Nat := 118140960795 + 131681 * 2 ^ 59
def prefixEnd_131681 : Nat := 4983230072969 + 3 ^ 40 * 131681 * 2
def baseEnd_131681 : Nat := 6678088500227608017967

theorem tailTrace_131681 : CollatzResearch.WordTrace tailWord_131681 prefixEnd_131681 6678088500227608017967 := by
  unfold tailWord_131681
  simp only [CollatzResearch.WordTrace]
  refine ⟨4802800635949701169442897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3201867090633134112961931 4802800635949701169442897)
  ·
    refine ⟨3602100476962275877082173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4802800635949701169442897 3602100476962275877082173)
    ·
      refine ⟨1350787678860853453905815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3602100476962275877082173 1350787678860853453905815)
      ·
        refine ⟨2026181518291280180858723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350787678860853453905815 2026181518291280180858723)
        ·
          refine ⟨3039272277436920271288085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026181518291280180858723 3039272277436920271288085)
          ·
            refine ⟨142465888004855637716629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3039272277436920271288085 142465888004855637716629)
            ·
              refine ⟨6678088500227608017967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142465888004855637716629 6678088500227608017967)
              ·
                rfl

theorem cell20_131681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 6].length) (baseStart_131681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131681 prefixEnd_131681 := by exact prefixLift 131681
  have htrace : WordTrace (prefixWord ++ tailWord_131681) baseStart_131681 baseEnd_131681 := by
    simpa [prefixWord, tailWord_131681, baseEnd_131681] using wordTrace_append hprefix tailTrace_131681
  have hstable : (prefixWord ++ tailWord_131681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131681).length < 2 ^ (prefixWord ++ tailWord_131681).sum := by decide
  have hdescent : baseEnd_131681 < baseStart_131681 := by decide
  rcases family_descends (prefixWord ++ tailWord_131681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131698 : List Nat := [3, 2, 1, 2, 4, 1, 2, 5]
def baseStart_131698 : Nat := 118140960795 + 131698 * 2 ^ 59
def prefixEnd_131698 : Nat := 4983230072969 + 3 ^ 40 * 131698 * 2
def baseEnd_131698 : Nat := 20036851921757322864989

theorem tailTrace_131698 : CollatzResearch.WordTrace tailWord_131698 prefixEnd_131698 20036851921757322864989 := by
  unfold tailWord_131698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1200855169222028268202937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3202280451258742048541165 1200855169222028268202937)
  ·
    refine ⟨900641376916521201152203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1200855169222028268202937 900641376916521201152203)
    ·
      refine ⟨1350962065374781801728305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900641376916521201152203 1350962065374781801728305)
      ·
        refine ⟨1013221549031086351296229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1350962065374781801728305 1013221549031086351296229)
        ·
          refine ⟨189979040443328690868043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1013221549031086351296229 189979040443328690868043)
          ·
            refine ⟨284968560664993036302065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189979040443328690868043 284968560664993036302065)
            ·
              refine ⟨213726420498744777226549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284968560664993036302065 213726420498744777226549)
              ·
                refine ⟨20036851921757322864989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213726420498744777226549 20036851921757322864989)
                ·
                  rfl

theorem cell20_131698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_131698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131698 prefixEnd_131698 := by exact prefixLift 131698
  have htrace : WordTrace (prefixWord ++ tailWord_131698) baseStart_131698 baseEnd_131698 := by
    simpa [prefixWord, tailWord_131698, baseEnd_131698] using wordTrace_append hprefix tailTrace_131698
  have hstable : (prefixWord ++ tailWord_131698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131698).length < 2 ^ (prefixWord ++ tailWord_131698).sum := by decide
  have hdescent : baseEnd_131698 < baseStart_131698 := by decide
  rcases family_descends (prefixWord ++ tailWord_131698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131705 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 3]
def baseStart_131705 : Nat := 118140960795 + 131705 * 2 ^ 59
def prefixEnd_131705 : Nat := 4983230072969 + 3 ^ 40 * 131705 * 2
def baseEnd_131705 : Nat := 60113750756011055361605

theorem tailTrace_131705 : CollatzResearch.WordTrace tailWord_131705 prefixEnd_131705 60113750756011055361605 := by
  unfold tailWord_131705
  simp only [CollatzResearch.WordTrace]
  refine ⟨4803675987862753268316569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3202450658575168845544379 4803675987862753268316569)
  ·
    refine ⟨3602756990897064951237427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4803675987862753268316569 3602756990897064951237427)
    ·
      refine ⟨5404135486345597426856141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3602756990897064951237427 5404135486345597426856141)
      ·
        refine ⟨2026550807379599035071053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5404135486345597426856141 2026550807379599035071053)
        ·
          refine ⟨759956552767349638151645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2026550807379599035071053 759956552767349638151645)
          ·
            refine ⟨284983707287756114306867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759956552767349638151645 284983707287756114306867)
            ·
              refine ⟨427475560931634171460301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284983707287756114306867 427475560931634171460301)
              ·
                refine ⟨160303335349362814297613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427475560931634171460301 160303335349362814297613)
                ·
                  refine ⟨60113750756011055361605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160303335349362814297613 60113750756011055361605)
                  ·
                    rfl

theorem cell20_131705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_131705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131705 prefixEnd_131705 := by exact prefixLift 131705
  have htrace : WordTrace (prefixWord ++ tailWord_131705) baseStart_131705 baseEnd_131705 := by
    simpa [prefixWord, tailWord_131705, baseEnd_131705] using wordTrace_append hprefix tailTrace_131705
  have hstable : (prefixWord ++ tailWord_131705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131705).length < 2 ^ (prefixWord ++ tailWord_131705).sum := by decide
  have hdescent : baseEnd_131705 < baseStart_131705 := by decide
  rcases family_descends (prefixWord ++ tailWord_131705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131774 : List Nat := [4, 2, 1, 1, 2, 1, 5, 4]
def baseStart_131774 : Nat := 118140960795 + 131774 * 2 ^ 59
def prefixEnd_131774 : Nat := 4983230072969 + 3 ^ 40 * 131774 * 2
def baseEnd_131774 : Nat := 20048414745384494020441

theorem tailTrace_131774 : CollatzResearch.WordTrace tailWord_131774 prefixEnd_131774 20048414745384494020441 := by
  unfold tailWord_131774
  simp only [CollatzResearch.WordTrace]
  refine ⟨600774078076597256572297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3204128416408518701718917 600774078076597256572297)
  ·
    refine ⟨450580558557447942429223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 600774078076597256572297 450580558557447942429223)
    ·
      refine ⟨675870837836171913643835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450580558557447942429223 675870837836171913643835)
      ·
        refine ⟨1013806256754257870465753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675870837836171913643835 1013806256754257870465753)
        ·
          refine ⟨760354692565693402849315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1013806256754257870465753 760354692565693402849315)
          ·
            refine ⟨1140532038848540104273973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760354692565693402849315 1140532038848540104273973)
            ·
              refine ⟨106924878642050634775685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1140532038848540104273973 106924878642050634775685)
              ·
                refine ⟨20048414745384494020441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106924878642050634775685 20048414745384494020441)
                ·
                  rfl

theorem cell20_131774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_131774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131774 prefixEnd_131774 := by exact prefixLift 131774
  have htrace : WordTrace (prefixWord ++ tailWord_131774) baseStart_131774 baseEnd_131774 := by
    simpa [prefixWord, tailWord_131774, baseEnd_131774] using wordTrace_append hprefix tailTrace_131774
  have hstable : (prefixWord ++ tailWord_131774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131774).length < 2 ^ (prefixWord ++ tailWord_131774).sum := by decide
  have hdescent : baseEnd_131774 < baseStart_131774 := by decide
  rcases family_descends (prefixWord ++ tailWord_131774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131802 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_131802 : Nat := 118140960795 + 131802 * 2 ^ 59
def prefixEnd_131802 : Nat := 4983230072969 + 3 ^ 40 * 131802 * 2
def baseEnd_131802 : Nat := 60158024199109829127875

theorem tailTrace_131802 : CollatzResearch.WordTrace tailWord_131802 prefixEnd_131802 60158024199109829127875 := by
  unfold tailWord_131802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201803467127834708649415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3204809245674225889731773 1201803467127834708649415)
  ·
    refine ⟨1802705200691752062974123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1201803467127834708649415 1802705200691752062974123)
    ·
      refine ⟨2704057801037628094461185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1802705200691752062974123 2704057801037628094461185)
      ·
        refine ⟨2028043350778221070845889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2704057801037628094461185 2028043350778221070845889)
        ·
          refine ⟨1521032513083665803134417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2028043350778221070845889 1521032513083665803134417)
          ·
            refine ⟨1140774384812749352350813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521032513083665803134417 1140774384812749352350813)
            ·
              refine ⟨427790394304781007131555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140774384812749352350813 427790394304781007131555)
              ·
                refine ⟨641685591457171510697333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427790394304781007131555 641685591457171510697333)
                ·
                  refine ⟨60158024199109829127875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 641685591457171510697333 60158024199109829127875)
                  ·
                    rfl

theorem cell20_131802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_131802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131802 prefixEnd_131802 := by exact prefixLift 131802
  have htrace : WordTrace (prefixWord ++ tailWord_131802) baseStart_131802 baseEnd_131802 := by
    simpa [prefixWord, tailWord_131802, baseEnd_131802] using wordTrace_append hprefix tailTrace_131802
  have hstable : (prefixWord ++ tailWord_131802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131802).length < 2 ^ (prefixWord ++ tailWord_131802).sum := by decide
  have hdescent : baseEnd_131802 < baseStart_131802 := by decide
  rcases family_descends (prefixWord ++ tailWord_131802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131826 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_131826 : Nat := 118140960795 + 131826 * 2 ^ 59
def prefixEnd_131826 : Nat := 4983230072969 + 3 ^ 40 * 131826 * 2
def baseEnd_131826 : Nat := 60168978453072412327777

theorem tailTrace_131826 : CollatzResearch.WordTrace tailWord_131826 prefixEnd_131826 60168978453072412327777 := by
  unfold tailWord_131826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202022305106097733367833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3205392813616260622314221 1202022305106097733367833)
  ·
    refine ⟨901516728829573300025875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1202022305106097733367833 901516728829573300025875)
    ·
      refine ⟨1352275093244359950038813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901516728829573300025875 1352275093244359950038813)
      ·
        refine ⟨507103159966634981264555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1352275093244359950038813 507103159966634981264555)
        ·
          refine ⟨760654739949952471896833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507103159966634981264555 760654739949952471896833)
          ·
            refine ⟨570491054962464353922625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760654739949952471896833 570491054962464353922625)
            ·
              refine ⟨427868291221848265441969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570491054962464353922625 427868291221848265441969)
              ·
                refine ⟨320901218416386199081477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427868291221848265441969 320901218416386199081477)
                ·
                  refine ⟨60168978453072412327777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320901218416386199081477 60168978453072412327777)
                  ·
                    rfl

theorem cell20_131826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_131826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131826 prefixEnd_131826 := by exact prefixLift 131826
  have htrace : WordTrace (prefixWord ++ tailWord_131826) baseStart_131826 baseEnd_131826 := by
    simpa [prefixWord, tailWord_131826, baseEnd_131826] using wordTrace_append hprefix tailTrace_131826
  have hstable : (prefixWord ++ tailWord_131826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131826).length < 2 ^ (prefixWord ++ tailWord_131826).sum := by decide
  have hdescent : baseEnd_131826 < baseStart_131826 := by decide
  rcases family_descends (prefixWord ++ tailWord_131826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131871 : List Nat := [1, 1, 2, 4, 2, 3, 2, 5]
def baseStart_131871 : Nat := 118140960795 + 131871 * 2 ^ 59
def prefixEnd_131871 : Nat := 4983230072969 + 3 ^ 40 * 131871 * 2
def baseEnd_131871 : Nat := 20063172559750751942531

theorem tailTrace_131871 : CollatzResearch.WordTrace tailWord_131871 prefixEnd_131871 20063172559750751942531 := by
  unfold tailWord_131871
  simp only [CollatzResearch.WordTrace]
  refine ⟨4809730505261363618859467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3206487003507575745906311 4809730505261363618859467)
  ·
    refine ⟨7214595757892045428289201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4809730505261363618859467 7214595757892045428289201)
    ·
      refine ⟨5410946818419034071216901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7214595757892045428289201 5410946818419034071216901)
      ·
        refine ⟨1014552528453568888353169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5410946818419034071216901 1014552528453568888353169)
        ·
          refine ⟨760914396340176666264877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014552528453568888353169 760914396340176666264877)
          ·
            refine ⟨285342898627566249849329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 760914396340176666264877 285342898627566249849329)
            ·
              refine ⟨214007173970674687386997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285342898627566249849329 214007173970674687386997)
              ·
                refine ⟨20063172559750751942531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214007173970674687386997 20063172559750751942531)
                ·
                  rfl

theorem cell20_131871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_131871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131871 prefixEnd_131871 := by exact prefixLift 131871
  have htrace : WordTrace (prefixWord ++ tailWord_131871) baseStart_131871 baseEnd_131871 := by
    simpa [prefixWord, tailWord_131871, baseEnd_131871] using wordTrace_append hprefix tailTrace_131871
  have hstable : (prefixWord ++ tailWord_131871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131871).length < 2 ^ (prefixWord ++ tailWord_131871).sum := by decide
  have hdescent : baseEnd_131871 < baseStart_131871 := by decide
  rcases family_descends (prefixWord ++ tailWord_131871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131874 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 3]
def baseStart_131874 : Nat := 118140960795 + 131874 * 2 ^ 59
def prefixEnd_131874 : Nat := 4983230072969 + 3 ^ 40 * 131874 * 2
def baseEnd_131874 : Nat := 60190886960997578727581

theorem tailTrace_131874 : CollatzResearch.WordTrace tailWord_131874 prefixEnd_131874 60190886960997578727581 := by
  unfold tailWord_131874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202459981062623782804669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3206559949500330087479117 1202459981062623782804669)
  ·
    refine ⟨450922492898483918551751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1202459981062623782804669 450922492898483918551751)
    ·
      refine ⟨676383739347725877827627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450922492898483918551751 676383739347725877827627)
      ·
        refine ⟨1014575609021588816741441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676383739347725877827627 1014575609021588816741441)
        ·
          refine ⟨760931706766191612556081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014575609021588816741441 760931706766191612556081)
          ·
            refine ⟨570698780074643709417061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760931706766191612556081 570698780074643709417061)
            ·
              refine ⟨107006021263995695515699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 570698780074643709417061 107006021263995695515699)
              ·
                refine ⟨160509031895993543273549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107006021263995695515699 160509031895993543273549)
                ·
                  refine ⟨60190886960997578727581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160509031895993543273549 60190886960997578727581)
                  ·
                    rfl

theorem cell20_131874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_131874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131874 prefixEnd_131874 := by exact prefixLift 131874
  have htrace : WordTrace (prefixWord ++ tailWord_131874) baseStart_131874 baseEnd_131874 := by
    simpa [prefixWord, tailWord_131874, baseEnd_131874] using wordTrace_append hprefix tailTrace_131874
  have hstable : (prefixWord ++ tailWord_131874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131874).length < 2 ^ (prefixWord ++ tailWord_131874).sum := by decide
  have hdescent : baseEnd_131874 < baseStart_131874 := by decide
  rcases family_descends (prefixWord ++ tailWord_131874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131940 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_131940 : Nat := 118140960795 + 131940 * 2 ^ 59
def prefixEnd_131940 : Nat := 4983230072969 + 3 ^ 40 * 131940 * 2
def baseEnd_131940 : Nat := 60221011159394682527311

theorem tailTrace_131940 : CollatzResearch.WordTrace tailWord_131940 prefixEnd_131940 60221011159394682527311 := by
  unfold tailWord_131940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406123571005694201560637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3208164761340925602080849 2406123571005694201560637)
  ·
    refine ⟨902296339127135325585239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2406123571005694201560637 902296339127135325585239)
    ·
      refine ⟨1353444508690702988377859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 902296339127135325585239 1353444508690702988377859)
      ·
        refine ⟨2030166763036054482566789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353444508690702988377859 2030166763036054482566789)
        ·
          refine ⟨380656268069260215481273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2030166763036054482566789 380656268069260215481273)
          ·
            refine ⟨285492201051945161610955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380656268069260215481273 285492201051945161610955)
            ·
              refine ⟨428238301577917742416433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285492201051945161610955 428238301577917742416433)
              ·
                refine ⟨321178726183438306812325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428238301577917742416433 321178726183438306812325)
                ·
                  refine ⟨60221011159394682527311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321178726183438306812325 60221011159394682527311)
                  ·
                    rfl

theorem cell20_131940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_131940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131940 prefixEnd_131940 := by exact prefixLift 131940
  have htrace : WordTrace (prefixWord ++ tailWord_131940) baseStart_131940 baseEnd_131940 := by
    simpa [prefixWord, tailWord_131940, baseEnd_131940] using wordTrace_append hprefix tailTrace_131940
  have hstable : (prefixWord ++ tailWord_131940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131940).length < 2 ^ (prefixWord ++ tailWord_131940).sum := by decide
  have hdescent : baseEnd_131940 < baseStart_131940 := by decide
  rcases family_descends (prefixWord ++ tailWord_131940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131957 : List Nat := [1, 3, 4, 1, 1, 2, 1, 5, 2]
def baseStart_131957 : Nat := 118140960795 + 131957 * 2 ^ 59
def prefixEnd_131957 : Nat := 4983230072969 + 3 ^ 40 * 131957 * 2
def baseEnd_131957 : Nat := 60228770422618178960575

theorem tailTrace_131957 : CollatzResearch.WordTrace tailWord_131957 prefixEnd_131957 60228770422618178960575 := by
  unfold tailWord_131957
  simp only [CollatzResearch.WordTrace]
  refine ⟨4812867182949800306490125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3208578121966533537660083 4812867182949800306490125)
  ·
    refine ⟨1804825193606175114933797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4812867182949800306490125 1804825193606175114933797)
    ·
      refine ⟨338404723801157834050087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1804825193606175114933797 338404723801157834050087)
      ·
        refine ⟨507607085701736751075131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338404723801157834050087 507607085701736751075131)
        ·
          refine ⟨761410628552605126612697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507607085701736751075131 761410628552605126612697)
          ·
            refine ⟨571057971414453844959523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761410628552605126612697 571057971414453844959523)
            ·
              refine ⟨856586957121680767439285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571057971414453844959523 856586957121680767439285)
              ·
                refine ⟨80305027230157571947433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 856586957121680767439285 80305027230157571947433)
                ·
                  refine ⟨60228770422618178960575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80305027230157571947433 60228770422618178960575)
                  ·
                    rfl

theorem cell20_131957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_131957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131957 prefixEnd_131957 := by exact prefixLift 131957
  have htrace : WordTrace (prefixWord ++ tailWord_131957) baseStart_131957 baseEnd_131957 := by
    simpa [prefixWord, tailWord_131957, baseEnd_131957] using wordTrace_append hprefix tailTrace_131957
  have hstable : (prefixWord ++ tailWord_131957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131957).length < 2 ^ (prefixWord ++ tailWord_131957).sum := by decide
  have hdescent : baseEnd_131957 < baseStart_131957 := by decide
  rcases family_descends (prefixWord ++ tailWord_131957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131978 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_131978 : Nat := 118140960795 + 131978 * 2 ^ 59
def prefixEnd_131978 : Nat := 4983230072969 + 3 ^ 40 * 131978 * 2
def baseEnd_131978 : Nat := 60238355394835439260489

theorem tailTrace_131978 : CollatzResearch.WordTrace tailWord_131978 prefixEnd_131978 60238355394835439260489 := by
  unfold tailWord_131978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203408278968430223251147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3209088743915813928669725 1203408278968430223251147)
  ·
    refine ⟨1805112418452645334876721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1203408278968430223251147 1805112418452645334876721)
    ·
      refine ⟨1353834313839484001157541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1805112418452645334876721 1353834313839484001157541)
      ·
        refine ⟨253843933844903250217039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1353834313839484001157541 253843933844903250217039)
        ·
          refine ⟨380765900767354875325559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253843933844903250217039 380765900767354875325559)
          ·
            refine ⟨571148851151032312988339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380765900767354875325559 571148851151032312988339)
            ·
              refine ⟨856723276726548469482509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571148851151032312988339 856723276726548469482509)
              ·
                refine ⟨321271228772455676055941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856723276726548469482509 321271228772455676055941)
                ·
                  refine ⟨60238355394835439260489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321271228772455676055941 60238355394835439260489)
                  ·
                    rfl

theorem cell20_131978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_131978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131978 prefixEnd_131978 := by exact prefixLift 131978
  have htrace : WordTrace (prefixWord ++ tailWord_131978) baseStart_131978 baseEnd_131978 := by
    simpa [prefixWord, tailWord_131978, baseEnd_131978] using wordTrace_append hprefix tailTrace_131978
  have hstable : (prefixWord ++ tailWord_131978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131978).length < 2 ^ (prefixWord ++ tailWord_131978).sum := by decide
  have hdescent : baseEnd_131978 < baseStart_131978 := by decide
  rcases family_descends (prefixWord ++ tailWord_131978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131988 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 3]
def baseStart_131988 : Nat := 118140960795 + 131988 * 2 ^ 59
def prefixEnd_131988 : Nat := 4983230072969 + 3 ^ 40 * 131988 * 2
def baseEnd_131988 : Nat := 60242919667319848927115

theorem tailTrace_131988 : CollatzResearch.WordTrace tailWord_131988 prefixEnd_131988 60242919667319848927115 := by
  unfold tailWord_131988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406998922918746300434309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3209331897224995067245745 2406998922918746300434309)
  ·
    refine ⟨451312298047264931331433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2406998922918746300434309 451312298047264931331433)
    ·
      refine ⟨338484223535448698498575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451312298047264931331433 338484223535448698498575)
      ·
        refine ⟨507726335303173047747863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338484223535448698498575 507726335303173047747863)
        ·
          refine ⟨761589502954759571621795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507726335303173047747863 761589502954759571621795)
          ·
            refine ⟨1142384254432139357432693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761589502954759571621795 1142384254432139357432693)
            ·
              refine ⟨107098523853013064759315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1142384254432139357432693 107098523853013064759315)
              ·
                refine ⟨160647785779519597138973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107098523853013064759315 160647785779519597138973)
                ·
                  refine ⟨60242919667319848927115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160647785779519597138973 60242919667319848927115)
                  ·
                    rfl

theorem cell20_131988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_131988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_131988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_131988 prefixEnd_131988 := by exact prefixLift 131988
  have htrace : WordTrace (prefixWord ++ tailWord_131988) baseStart_131988 baseEnd_131988 := by
    simpa [prefixWord, tailWord_131988, baseEnd_131988] using wordTrace_append hprefix tailTrace_131988
  have hstable : (prefixWord ++ tailWord_131988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131988).length < 2 ^ (prefixWord ++ tailWord_131988).sum := by decide
  have hdescent : baseEnd_131988 < baseStart_131988 := by decide
  rcases family_descends (prefixWord ++ tailWord_131988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132002 : List Nat := [3, 3, 1, 2, 2, 1, 4, 4]
def baseStart_132002 : Nat := 118140960795 + 132002 * 2 ^ 59
def prefixEnd_132002 : Nat := 4983230072969 + 3 ^ 40 * 132002 * 2
def baseEnd_132002 : Nat := 20083103216266007486797

theorem tailTrace_132002 : CollatzResearch.WordTrace tailWord_132002 prefixEnd_132002 20083103216266007486797 := by
  unfold tailWord_132002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203627116946693247969565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3209672311857848661252173 1203627116946693247969565)
  ·
    refine ⟨451360168855009967988587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1203627116946693247969565 451360168855009967988587)
    ·
      refine ⟨677040253282514951982881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451360168855009967988587 677040253282514951982881)
      ·
        refine ⟨507780189961886213987161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 677040253282514951982881 507780189961886213987161)
        ·
          refine ⟨380835142471414660490371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507780189961886213987161 380835142471414660490371)
          ·
            refine ⟨571252713707121990735557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380835142471414660490371 571252713707121990735557)
            ·
              refine ⟨107109883820085373262917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 571252713707121990735557 107109883820085373262917)
              ·
                refine ⟨20083103216266007486797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107109883820085373262917 20083103216266007486797)
                ·
                  rfl

theorem cell20_132002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_132002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132002 prefixEnd_132002 := by exact prefixLift 132002
  have htrace : WordTrace (prefixWord ++ tailWord_132002) baseStart_132002 baseEnd_132002 := by
    simpa [prefixWord, tailWord_132002, baseEnd_132002] using wordTrace_append hprefix tailTrace_132002
  have hstable : (prefixWord ++ tailWord_132002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132002).length < 2 ^ (prefixWord ++ tailWord_132002).sum := by decide
  have hdescent : baseEnd_132002 < baseStart_132002 := by decide
  rcases family_descends (prefixWord ++ tailWord_132002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132030 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_132030 : Nat := 118140960795 + 132030 * 2 ^ 59
def prefixEnd_132030 : Nat := 4983230072969 + 3 ^ 40 * 132030 * 2
def baseEnd_132030 : Nat := 60262089611754369526943

theorem tailTrace_132030 : CollatzResearch.WordTrace tailWord_132030 prefixEnd_132030 60262089611754369526943 := by
  unfold tailWord_132030
  simp only [CollatzResearch.WordTrace]
  refine ⟨601941213960666721737193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3210353141123555849265029 601941213960666721737193)
  ·
    refine ⟨451455910470500041302895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 601941213960666721737193 451455910470500041302895)
    ·
      refine ⟨677183865705750061954343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451455910470500041302895 677183865705750061954343)
      ·
        refine ⟨1015775798558625092931515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677183865705750061954343 1015775798558625092931515)
        ·
          refine ⟨1523663697837937639397273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015775798558625092931515 1523663697837937639397273)
          ·
            refine ⟨1142747773378453229547955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1523663697837937639397273 1142747773378453229547955)
            ·
              refine ⟨1714121660067679844321933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142747773378453229547955 1714121660067679844321933)
              ·
                refine ⟨642795622525379941620725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1714121660067679844321933 642795622525379941620725)
                ·
                  refine ⟨60262089611754369526943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 642795622525379941620725 60262089611754369526943)
                  ·
                    rfl

theorem cell20_132030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_132030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132030 prefixEnd_132030 := by exact prefixLift 132030
  have htrace : WordTrace (prefixWord ++ tailWord_132030) baseStart_132030 baseEnd_132030 := by
    simpa [prefixWord, tailWord_132030, baseEnd_132030] using wordTrace_append hprefix tailTrace_132030
  have hstable : (prefixWord ++ tailWord_132030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132030).length < 2 ^ (prefixWord ++ tailWord_132030).sum := by decide
  have hdescent : baseEnd_132030 < baseStart_132030 := by decide
  rcases family_descends (prefixWord ++ tailWord_132030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132047 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 3]
def baseStart_132047 : Nat := 118140960795 + 132047 * 2 ^ 59
def prefixEnd_132047 : Nat := 4983230072969 + 3 ^ 40 * 132047 * 2
def baseEnd_132047 : Nat := 60269848874977865960207

theorem tailTrace_132047 : CollatzResearch.WordTrace tailWord_132047 prefixEnd_132047 60269848874977865960207 := by
  unfold tailWord_132047
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816149752623745677266395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3210766501749163784844263 4816149752623745677266395)
  ·
    refine ⟨7224224628935618515899593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4816149752623745677266395 7224224628935618515899593)
    ·
      refine ⟨5418168471701713886924695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7224224628935618515899593 5418168471701713886924695)
      ·
        refine ⟨8127252707552570830387043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418168471701713886924695 8127252707552570830387043)
        ·
          refine ⟨12190879061328856245580565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8127252707552570830387043 12190879061328856245580565)
          ·
            refine ⟨571447455999790136511589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12190879061328856245580565 571447455999790136511589)
            ·
              refine ⟨107146397999960650595923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 571447455999790136511589 107146397999960650595923)
              ·
                refine ⟨160719596999940975893885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107146397999960650595923 160719596999940975893885)
                ·
                  refine ⟨60269848874977865960207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160719596999940975893885 60269848874977865960207)
                  ·
                    rfl

theorem cell20_132047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 3].length) (baseStart_132047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132047 prefixEnd_132047 := by exact prefixLift 132047
  have htrace : WordTrace (prefixWord ++ tailWord_132047) baseStart_132047 baseEnd_132047 := by
    simpa [prefixWord, tailWord_132047, baseEnd_132047] using wordTrace_append hprefix tailTrace_132047
  have hstable : (prefixWord ++ tailWord_132047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132047).length < 2 ^ (prefixWord ++ tailWord_132047).sum := by decide
  have hdescent : baseEnd_132047 < baseStart_132047 := by decide
  rcases family_descends (prefixWord ++ tailWord_132047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132061 : List Nat := [1, 4, 3, 1, 2, 1, 2, 6]
def baseStart_132061 : Nat := 118140960795 + 132061 * 2 ^ 59
def prefixEnd_132061 : Nat := 4983230072969 + 3 ^ 40 * 132061 * 2
def baseEnd_132061 : Nat := 20092079618818679831161

theorem tailTrace_132061 : CollatzResearch.WordTrace tailWord_132061 prefixEnd_132061 20092079618818679831161 := by
  unfold tailWord_132061
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816660374573026068276037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3211106916382017378850691 4816660374573026068276037)
  ·
    refine ⟨903123820232442387801757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4816660374573026068276037 903123820232442387801757)
    ·
      refine ⟨338671432587165895425659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 903123820232442387801757 338671432587165895425659)
      ·
        refine ⟨508007148880748843138489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338671432587165895425659 508007148880748843138489)
        ·
          refine ⟨381005361660561632353867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508007148880748843138489 381005361660561632353867)
          ·
            refine ⟨571508042490842448530801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381005361660561632353867 571508042490842448530801)
            ·
              refine ⟨428631031868131836398101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571508042490842448530801 428631031868131836398101)
              ·
                refine ⟨20092079618818679831161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 428631031868131836398101 20092079618818679831161)
                ·
                  rfl

theorem cell20_132061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_132061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132061 prefixEnd_132061 := by exact prefixLift 132061
  have htrace : WordTrace (prefixWord ++ tailWord_132061) baseStart_132061 baseEnd_132061 := by
    simpa [prefixWord, tailWord_132061, baseEnd_132061] using wordTrace_append hprefix tailTrace_132061
  have hstable : (prefixWord ++ tailWord_132061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132061).length < 2 ^ (prefixWord ++ tailWord_132061).sum := by decide
  have hdescent : baseEnd_132061 < baseStart_132061 := by decide
  rcases family_descends (prefixWord ++ tailWord_132061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132202 : List Nat := [3, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_132202 : Nat := 118140960795 + 132202 * 2 ^ 59
def prefixEnd_132202 : Nat := 4983230072969 + 3 ^ 40 * 132202 * 2
def baseEnd_132202 : Nat := 60340595098486215792907

theorem tailTrace_132202 : CollatzResearch.WordTrace tailWord_132202 prefixEnd_132202 60340595098486215792907 := by
  unfold tailWord_132202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205450766765551787289715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3214535378041471432772573 1205450766765551787289715)
  ·
    refine ⟨1808176150148327680934573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1205450766765551787289715 1808176150148327680934573)
    ·
      refine ⟨678066056305622880350465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1808176150148327680934573 678066056305622880350465)
      ·
        refine ⟨508549542229217160262849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678066056305622880350465 508549542229217160262849)
        ·
          refine ⟨381412156671912870197137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508549542229217160262849 381412156671912870197137)
          ·
            refine ⟨286059117503934652647853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381412156671912870197137 286059117503934652647853)
            ·
              refine ⟨107272169063975494742945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286059117503934652647853 107272169063975494742945)
              ·
                refine ⟨80454126797981621057209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107272169063975494742945 80454126797981621057209)
                ·
                  refine ⟨60340595098486215792907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80454126797981621057209 60340595098486215792907)
                  ·
                    rfl

theorem cell20_132202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_132202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132202 prefixEnd_132202 := by exact prefixLift 132202
  have htrace : WordTrace (prefixWord ++ tailWord_132202) baseStart_132202 baseEnd_132202 := by
    simpa [prefixWord, tailWord_132202, baseEnd_132202] using wordTrace_append hprefix tailTrace_132202
  have hstable : (prefixWord ++ tailWord_132202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132202).length < 2 ^ (prefixWord ++ tailWord_132202).sum := by decide
  have hdescent : baseEnd_132202 < baseStart_132202 := by decide
  rcases family_descends (prefixWord ++ tailWord_132202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132206 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_132206 : Nat := 118140960795 + 132206 * 2 ^ 59
def prefixEnd_132206 : Nat := 4983230072969 + 3 ^ 40 * 132206 * 2
def baseEnd_132206 : Nat := 60342420807479979659557

theorem tailTrace_132206 : CollatzResearch.WordTrace tailWord_132206 prefixEnd_132206 60342420807479979659557 := by
  unfold tailWord_132206
  simp only [CollatzResearch.WordTrace]
  refine ⟨602743619880964479038059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3214632639365143888202981 602743619880964479038059)
  ·
    refine ⟨904115429821446718557089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 602743619880964479038059 904115429821446718557089)
    ·
      refine ⟨678086572366085038917817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 904115429821446718557089 678086572366085038917817)
      ·
        refine ⟨508564929274563779188363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678086572366085038917817 508564929274563779188363)
        ·
          refine ⟨762847393911845668782545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508564929274563779188363 762847393911845668782545)
          ·
            refine ⟨572135545433884251586909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762847393911845668782545 572135545433884251586909)
            ·
              refine ⟨214550829537706594345091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 572135545433884251586909 214550829537706594345091)
              ·
                refine ⟨321826244306559891517637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214550829537706594345091 321826244306559891517637)
                ·
                  refine ⟨60342420807479979659557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321826244306559891517637 60342420807479979659557)
                  ·
                    rfl

theorem cell20_132206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_132206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132206 prefixEnd_132206 := by exact prefixLift 132206
  have htrace : WordTrace (prefixWord ++ tailWord_132206) baseStart_132206 baseEnd_132206 := by
    simpa [prefixWord, tailWord_132206, baseEnd_132206] using wordTrace_append hprefix tailTrace_132206
  have hstable : (prefixWord ++ tailWord_132206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132206).length < 2 ^ (prefixWord ++ tailWord_132206).sum := by decide
  have hdescent : baseEnd_132206 < baseStart_132206 := by decide
  rcases family_descends (prefixWord ++ tailWord_132206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132220 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_132220 : Nat := 118140960795 + 132220 * 2 ^ 59
def prefixEnd_132220 : Nat := 4983230072969 + 3 ^ 40 * 132220 * 2
def baseEnd_132220 : Nat := 60348810788958153192833

theorem tailTrace_132220 : CollatzResearch.WordTrace tailWord_132220 prefixEnd_132220 60348810788958153192833 := by
  unfold tailWord_132220
  simp only [CollatzResearch.WordTrace]
  refine ⟨2411229790498498111657057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3214973053997997482209409 2411229790498498111657057)
  ·
    refine ⟨1808422342873873583742793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2411229790498498111657057 1808422342873873583742793)
    ·
      refine ⟨1356316757155405187807095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1808422342873873583742793 1356316757155405187807095)
      ·
        refine ⟨2034475135733107781710643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356316757155405187807095 2034475135733107781710643)
        ·
          refine ⟨3051712703599661672565965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2034475135733107781710643 3051712703599661672565965)
          ·
            refine ⟨1144392263849873127212237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3051712703599661672565965 1144392263849873127212237)
            ·
              refine ⟨429147098943702422704589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1144392263849873127212237 429147098943702422704589)
              ·
                refine ⟨160930162103888408514221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429147098943702422704589 160930162103888408514221)
                ·
                  refine ⟨60348810788958153192833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160930162103888408514221 60348810788958153192833)
                  ·
                    rfl

theorem cell20_132220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_132220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132220 prefixEnd_132220 := by exact prefixLift 132220
  have htrace : WordTrace (prefixWord ++ tailWord_132220) baseStart_132220 baseEnd_132220 := by
    simpa [prefixWord, tailWord_132220, baseEnd_132220] using wordTrace_append hprefix tailTrace_132220
  have hstable : (prefixWord ++ tailWord_132220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132220).length < 2 ^ (prefixWord ++ tailWord_132220).sum := by decide
  have hdescent : baseEnd_132220 < baseStart_132220 := by decide
  rcases family_descends (prefixWord ++ tailWord_132220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132234 : List Nat := [3, 1, 2, 3, 1, 1, 1, 8]
def baseStart_132234 : Nat := 118140960795 + 132234 * 2 ^ 59
def prefixEnd_132234 : Nat := 4983230072969 + 3 ^ 40 * 132234 * 2
def baseEnd_132234 : Nat := 20118400256812108908703

theorem tailTrace_132234 : CollatzResearch.WordTrace tailWord_132234 prefixEnd_132234 20118400256812108908703 := by
  unfold tailWord_132234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205742550736569153580939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3215313468630851076215837 1205742550736569153580939)
  ·
    refine ⟨1808613826104853730371409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1205742550736569153580939 1808613826104853730371409)
    ·
      refine ⟨1356460369578640297778557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1808613826104853730371409 1356460369578640297778557)
      ·
        refine ⟨508672638591990111666959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1356460369578640297778557 508672638591990111666959)
        ·
          refine ⟨763008957887985167500439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508672638591990111666959 763008957887985167500439)
          ·
            refine ⟨1144513436831977751250659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763008957887985167500439 1144513436831977751250659)
            ·
              refine ⟨1716770155247966626875989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144513436831977751250659 1716770155247966626875989)
              ·
                refine ⟨20118400256812108908703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1716770155247966626875989 20118400256812108908703)
                ·
                  rfl

theorem cell20_132234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_132234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132234 prefixEnd_132234 := by exact prefixLift 132234
  have htrace : WordTrace (prefixWord ++ tailWord_132234) baseStart_132234 baseEnd_132234 := by
    simpa [prefixWord, tailWord_132234, baseEnd_132234] using wordTrace_append hprefix tailTrace_132234
  have hstable : (prefixWord ++ tailWord_132234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132234).length < 2 ^ (prefixWord ++ tailWord_132234).sum := by decide
  have hdescent : baseEnd_132234 < baseStart_132234 := by decide
  rcases family_descends (prefixWord ++ tailWord_132234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132254 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_132254 : Nat := 118140960795 + 132254 * 2 ^ 59
def prefixEnd_132254 : Nat := 4983230072969 + 3 ^ 40 * 132254 * 2
def baseEnd_132254 : Nat := 60364329315405146059361

theorem tailTrace_132254 : CollatzResearch.WordTrace tailWord_132254 prefixEnd_132254 60364329315405146059361 := by
  unfold tailWord_132254
  simp only [CollatzResearch.WordTrace]
  refine ⟨602962457859227503756477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3215799775249213353367877 602962457859227503756477)
  ·
    refine ⟨226110921697210313908679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 602962457859227503756477 226110921697210313908679)
    ·
      refine ⟨339166382545815470863019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226110921697210313908679 339166382545815470863019)
      ·
        refine ⟨508749573818723206294529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339166382545815470863019 508749573818723206294529)
        ·
          refine ⟨381562180364042404720897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508749573818723206294529 381562180364042404720897)
          ·
            refine ⟨286171635273031803540673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381562180364042404720897 286171635273031803540673)
            ·
              refine ⟨214628726454773852655505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286171635273031803540673 214628726454773852655505)
              ·
                refine ⟨160971544841080389491629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214628726454773852655505 160971544841080389491629)
                ·
                  refine ⟨60364329315405146059361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160971544841080389491629 60364329315405146059361)
                  ·
                    rfl

theorem cell20_132254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_132254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132254 prefixEnd_132254 := by exact prefixLift 132254
  have htrace : WordTrace (prefixWord ++ tailWord_132254) baseStart_132254 baseEnd_132254 := by
    simpa [prefixWord, tailWord_132254, baseEnd_132254] using wordTrace_append hprefix tailTrace_132254
  have hstable : (prefixWord ++ tailWord_132254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132254).length < 2 ^ (prefixWord ++ tailWord_132254).sum := by decide
  have hdescent : baseEnd_132254 < baseStart_132254 := by decide
  rcases family_descends (prefixWord ++ tailWord_132254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132261 : List Nat := [1, 3, 1, 2, 1, 4, 4, 2, 2]
def baseStart_132261 : Nat := 118140960795 + 132261 * 2 ^ 59
def prefixEnd_132261 : Nat := 4983230072969 + 3 ^ 40 * 132261 * 2
def baseEnd_132261 : Nat := 60367524306144232825999

theorem tailTrace_132261 : CollatzResearch.WordTrace tailWord_132261 prefixEnd_132261 60367524306144232825999 := by
  unfold tailWord_132261
  simp only [CollatzResearch.WordTrace]
  refine ⟨4823954973848460225556637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3215969982565640150371091 4823954973848460225556637)
  ·
    refine ⟨1808983115193172584583739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4823954973848460225556637 1808983115193172584583739)
    ·
      refine ⟨2713474672789758876875609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1808983115193172584583739 2713474672789758876875609)
      ·
        refine ⟨2035106004592319157656707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2713474672789758876875609 2035106004592319157656707)
        ·
          refine ⟨3052659006888478736485061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2035106004592319157656707 3052659006888478736485061)
          ·
            refine ⟨572373563791589763090949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3052659006888478736485061 572373563791589763090949)
            ·
              refine ⟨107320043210923080579553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 572373563791589763090949 107320043210923080579553)
              ·
                refine ⟨80490032408192310434665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107320043210923080579553 80490032408192310434665)
                ·
                  refine ⟨60367524306144232825999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80490032408192310434665 60367524306144232825999)
                  ·
                    rfl

theorem cell20_132261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_132261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132261 prefixEnd_132261 := by exact prefixLift 132261
  have htrace : WordTrace (prefixWord ++ tailWord_132261) baseStart_132261 baseEnd_132261 := by
    simpa [prefixWord, tailWord_132261, baseEnd_132261] using wordTrace_append hprefix tailTrace_132261
  have hstable : (prefixWord ++ tailWord_132261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132261).length < 2 ^ (prefixWord ++ tailWord_132261).sum := by decide
  have hdescent : baseEnd_132261 < baseStart_132261 := by decide
  rcases family_descends (prefixWord ++ tailWord_132261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132278 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_132278 : Nat := 118140960795 + 132278 * 2 ^ 59
def prefixEnd_132278 : Nat := 4983230072969 + 3 ^ 40 * 132278 * 2
def baseEnd_132278 : Nat := 60375283569367729259263

theorem tailTrace_132278 : CollatzResearch.WordTrace tailWord_132278 prefixEnd_132278 60375283569367729259263 := by
  unfold tailWord_132278
  simp only [CollatzResearch.WordTrace]
  refine ⟨301535938424179508057843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3216383343191248085950325 301535938424179508057843)
  ·
    refine ⟨452303907636269262086765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301535938424179508057843 452303907636269262086765)
    ·
      refine ⟨169613965363600973282537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452303907636269262086765 169613965363600973282537)
      ·
        refine ⟨127210474022700729961903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169613965363600973282537 127210474022700729961903)
        ·
          refine ⟨190815711034051094942855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127210474022700729961903 190815711034051094942855)
          ·
            refine ⟨286223566551076642414283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190815711034051094942855 286223566551076642414283)
            ·
              refine ⟨429335349826614963621425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286223566551076642414283 429335349826614963621425)
              ·
                refine ⟨322001512369961222716069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429335349826614963621425 322001512369961222716069)
                ·
                  refine ⟨60375283569367729259263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322001512369961222716069 60375283569367729259263)
                  ·
                    rfl

theorem cell20_132278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_132278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132278 prefixEnd_132278 := by exact prefixLift 132278
  have htrace : WordTrace (prefixWord ++ tailWord_132278) baseStart_132278 baseEnd_132278 := by
    simpa [prefixWord, tailWord_132278, baseEnd_132278] using wordTrace_append hprefix tailTrace_132278
  have hstable : (prefixWord ++ tailWord_132278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132278).length < 2 ^ (prefixWord ++ tailWord_132278).sum := by decide
  have hdescent : baseEnd_132278 < baseStart_132278 := by decide
  rcases family_descends (prefixWord ++ tailWord_132278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132320 : List Nat := [2, 1, 1, 3, 1, 4, 2, 4, 2]
def baseStart_132320 : Nat := 118140960795 + 132320 * 2 ^ 59
def prefixEnd_132320 : Nat := 4983230072969 + 3 ^ 40 * 132320 * 2
def baseEnd_132320 : Nat := 60394453513802249859091

theorem tailTrace_132320 : CollatzResearch.WordTrace tailWord_132320 prefixEnd_132320 60394453513802249859091 := by
  unfold tailWord_132320
  simp only [CollatzResearch.WordTrace]
  refine ⟨2413053440317356650977207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3217404587089808867969609 2413053440317356650977207)
  ·
    refine ⟨3619580160476034976465811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2413053440317356650977207 3619580160476034976465811)
    ·
      refine ⟨5429370240714052464698717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3619580160476034976465811 5429370240714052464698717)
      ·
        refine ⟨2036013840267769674262019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5429370240714052464698717 2036013840267769674262019)
        ·
          refine ⟨3054020760401654511393029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036013840267769674262019 3054020760401654511393029)
          ·
            refine ⟨572628892575310220886193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3054020760401654511393029 572628892575310220886193)
            ·
              refine ⟨429471669431482665664645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572628892575310220886193 429471669431482665664645)
              ·
                refine ⟨80525938018402999812121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429471669431482665664645 80525938018402999812121)
                ·
                  refine ⟨60394453513802249859091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80525938018402999812121 60394453513802249859091)
                  ·
                    rfl

theorem cell20_132320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_132320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132320 prefixEnd_132320 := by exact prefixLift 132320
  have htrace : WordTrace (prefixWord ++ tailWord_132320) baseStart_132320 baseEnd_132320 := by
    simpa [prefixWord, tailWord_132320, baseEnd_132320] using wordTrace_append hprefix tailTrace_132320
  have hstable : (prefixWord ++ tailWord_132320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132320).length < 2 ^ (prefixWord ++ tailWord_132320).sum := by decide
  have hdescent : baseEnd_132320 < baseStart_132320 := by decide
  rcases family_descends (prefixWord ++ tailWord_132320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132334 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_132334 : Nat := 118140960795 + 132334 * 2 ^ 59
def prefixEnd_132334 : Nat := 4983230072969 + 3 ^ 40 * 132334 * 2
def baseEnd_132334 : Nat := 60400843495280423392367

theorem tailTrace_132334 : CollatzResearch.WordTrace tailWord_132334 prefixEnd_132334 60400843495280423392367 := by
  unfold tailWord_132334
  simp only [CollatzResearch.WordTrace]
  refine ⟨603327187822999211620507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3217745001722662461976037 603327187822999211620507)
  ·
    refine ⟨904990781734498817430761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 603327187822999211620507 904990781734498817430761)
    ·
      refine ⟨678743086300874113073071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 904990781734498817430761 678743086300874113073071)
      ·
        refine ⟨1018114629451311169609607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678743086300874113073071 1018114629451311169609607)
        ·
          refine ⟨1527171944176966754414411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1018114629451311169609607 1527171944176966754414411)
          ·
            refine ⟨2290757916265450131621617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1527171944176966754414411 2290757916265450131621617)
            ·
              refine ⟨1718068437199087598716213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2290757916265450131621617 1718068437199087598716213)
              ·
                refine ⟨161068915987414462379645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1718068437199087598716213 161068915987414462379645)
                ·
                  refine ⟨60400843495280423392367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161068915987414462379645 60400843495280423392367)
                  ·
                    rfl

theorem cell20_132334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_132334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132334 prefixEnd_132334 := by exact prefixLift 132334
  have htrace : WordTrace (prefixWord ++ tailWord_132334) baseStart_132334 baseEnd_132334 := by
    simpa [prefixWord, tailWord_132334, baseEnd_132334] using wordTrace_append hprefix tailTrace_132334
  have hstable : (prefixWord ++ tailWord_132334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132334).length < 2 ^ (prefixWord ++ tailWord_132334).sum := by decide
  have hdescent : baseEnd_132334 < baseStart_132334 := by decide
  rcases family_descends (prefixWord ++ tailWord_132334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132355 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_132355 : Nat := 118140960795 + 132355 * 2 ^ 59
def prefixEnd_132355 : Nat := 4983230072969 + 3 ^ 40 * 132355 * 2
def baseEnd_132355 : Nat := 60410428467497683692281

theorem tailTrace_132355 : CollatzResearch.WordTrace tailWord_132355 prefixEnd_132355 60410428467497683692281 := by
  unfold tailWord_132355
  simp only [CollatzResearch.WordTrace]
  refine ⟨4827383435507914279478519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3218255623671942852985679 4827383435507914279478519)
  ·
    refine ⟨7241075153261871419217779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4827383435507914279478519 7241075153261871419217779)
    ·
      refine ⟨10861612729892807128826669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7241075153261871419217779 10861612729892807128826669)
      ·
        refine ⟨4073104773709802673310001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10861612729892807128826669 4073104773709802673310001)
        ·
          refine ⟨3054828580282352004982501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4073104773709802673310001 3054828580282352004982501)
          ·
            refine ⟨572780358802941000934219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3054828580282352004982501 572780358802941000934219)
            ·
              refine ⟨859170538204411501401329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572780358802941000934219 859170538204411501401329)
              ·
                refine ⟨644377903653308626050997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 859170538204411501401329 644377903653308626050997)
                ·
                  refine ⟨60410428467497683692281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 644377903653308626050997 60410428467497683692281)
                  ·
                    rfl

theorem cell20_132355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_132355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132355 prefixEnd_132355 := by exact prefixLift 132355
  have htrace : WordTrace (prefixWord ++ tailWord_132355) baseStart_132355 baseEnd_132355 := by
    simpa [prefixWord, tailWord_132355, baseEnd_132355] using wordTrace_append hprefix tailTrace_132355
  have hstable : (prefixWord ++ tailWord_132355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132355).length < 2 ^ (prefixWord ++ tailWord_132355).sum := by decide
  have hdescent : baseEnd_132355 < baseStart_132355 := by decide
  rcases family_descends (prefixWord ++ tailWord_132355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132375 : List Nat := [1, 1, 3, 4, 1, 1, 5, 2, 2]
def baseStart_132375 : Nat := 118140960795 + 132375 * 2 ^ 59
def prefixEnd_132375 : Nat := 4983230072969 + 3 ^ 40 * 132375 * 2
def baseEnd_132375 : Nat := 60419557012466503025533

theorem tailTrace_132375 : CollatzResearch.WordTrace tailWord_132375 prefixEnd_132375 60419557012466503025533 := by
  unfold tailWord_132375
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828112895435457695206579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3218741930290305130137719 4828112895435457695206579)
  ·
    refine ⟨7242169343153186542809869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4828112895435457695206579 7242169343153186542809869)
    ·
      refine ⟨2715813503682444953553701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7242169343153186542809869 2715813503682444953553701)
      ·
        refine ⟨509215031940458428791319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2715813503682444953553701 509215031940458428791319)
        ·
          refine ⟨763822547910687643186979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509215031940458428791319 763822547910687643186979)
          ·
            refine ⟨1145733821866031464780469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763822547910687643186979 1145733821866031464780469)
            ·
              refine ⟨107412545799940449823169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1145733821866031464780469 107412545799940449823169)
              ·
                refine ⟨80559409349955337367377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107412545799940449823169 80559409349955337367377)
                ·
                  refine ⟨60419557012466503025533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80559409349955337367377 60419557012466503025533)
                  ·
                    rfl

theorem cell20_132375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 2].length) (baseStart_132375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132375 prefixEnd_132375 := by exact prefixLift 132375
  have htrace : WordTrace (prefixWord ++ tailWord_132375) baseStart_132375 baseEnd_132375 := by
    simpa [prefixWord, tailWord_132375, baseEnd_132375] using wordTrace_append hprefix tailTrace_132375
  have hstable : (prefixWord ++ tailWord_132375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132375).length < 2 ^ (prefixWord ++ tailWord_132375).sum := by decide
  have hdescent : baseEnd_132375 < baseStart_132375 := by decide
  rcases family_descends (prefixWord ++ tailWord_132375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132389 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 3]
def baseStart_132389 : Nat := 118140960795 + 132389 * 2 ^ 59
def prefixEnd_132389 : Nat := 4983230072969 + 3 ^ 40 * 132389 * 2
def baseEnd_132389 : Nat := 60425946993944676558809

theorem tailTrace_132389 : CollatzResearch.WordTrace tailWord_132389 prefixEnd_132389 60425946993944676558809 := by
  unfold tailWord_132389
  simp only [CollatzResearch.WordTrace]
  refine ⟨4828623517384738086216221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3219082344923158724144147 4828623517384738086216221)
  ·
    refine ⟨1810733819019276782331083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4828623517384738086216221 1810733819019276782331083)
    ·
      refine ⟨2716100728528915173496625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810733819019276782331083 2716100728528915173496625)
      ·
        refine ⟨2037075546396686380122469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2716100728528915173496625 2037075546396686380122469)
        ·
          refine ⟨381951664949378696272963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2037075546396686380122469 381951664949378696272963)
          ·
            refine ⟨572927497424068044409445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381951664949378696272963 572927497424068044409445)
            ·
              refine ⟨107423905767012758326771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 572927497424068044409445 107423905767012758326771)
              ·
                refine ⟨161135858650519137490157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107423905767012758326771 161135858650519137490157)
                ·
                  refine ⟨60425946993944676558809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161135858650519137490157 60425946993944676558809)
                  ·
                    rfl

theorem cell20_132389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_132389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132389 prefixEnd_132389 := by exact prefixLift 132389
  have htrace : WordTrace (prefixWord ++ tailWord_132389) baseStart_132389 baseEnd_132389 := by
    simpa [prefixWord, tailWord_132389, baseEnd_132389] using wordTrace_append hprefix tailTrace_132389
  have hstable : (prefixWord ++ tailWord_132389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132389).length < 2 ^ (prefixWord ++ tailWord_132389).sum := by decide
  have hdescent : baseEnd_132389 < baseStart_132389 := by decide
  rcases family_descends (prefixWord ++ tailWord_132389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132400 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_132400 : Nat := 118140960795 + 132400 * 2 ^ 59
def prefixEnd_132400 : Nat := 4983230072969 + 3 ^ 40 * 132400 * 2
def baseEnd_132400 : Nat := 60430967693677527192097

theorem tailTrace_132400 : CollatzResearch.WordTrace tailWord_132400 prefixEnd_132400 60430967693677527192097 := by
  unfold tailWord_132400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2414512360172443482433327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3219349813563257976577769 2414512360172443482433327)
  ·
    refine ⟨3621768540258665223649991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2414512360172443482433327 3621768540258665223649991)
    ·
      refine ⟨5432652810387997835474987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3621768540258665223649991 5432652810387997835474987)
      ·
        refine ⟨8148979215581996753212481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432652810387997835474987 8148979215581996753212481)
        ·
          refine ⟨6111734411686497564909361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8148979215581996753212481 6111734411686497564909361)
          ·
            refine ⟨4583800808764873173682021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6111734411686497564909361 4583800808764873173682021)
            ·
              refine ⟨859462651643413720065379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4583800808764873173682021 859462651643413720065379)
              ·
                refine ⟨1289193977465120580098069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 859462651643413720065379 1289193977465120580098069)
                ·
                  refine ⟨60430967693677527192097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1289193977465120580098069 60430967693677527192097)
                  ·
                    rfl

theorem cell20_132400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_132400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132400 prefixEnd_132400 := by exact prefixLift 132400
  have htrace : WordTrace (prefixWord ++ tailWord_132400) baseStart_132400 baseEnd_132400 := by
    simpa [prefixWord, tailWord_132400, baseEnd_132400] using wordTrace_append hprefix tailTrace_132400
  have hstable : (prefixWord ++ tailWord_132400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132400).length < 2 ^ (prefixWord ++ tailWord_132400).sum := by decide
  have hdescent : baseEnd_132400 < baseStart_132400 := by decide
  rcases family_descends (prefixWord ++ tailWord_132400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132448 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_132448 : Nat := 118140960795 + 132448 * 2 ^ 59
def prefixEnd_132448 : Nat := 4983230072969 + 3 ^ 40 * 132448 * 2
def baseEnd_132448 : Nat := 60452876201602693591901

theorem tailTrace_132448 : CollatzResearch.WordTrace tailWord_132448 prefixEnd_132448 60452876201602693591901 := by
  unfold tailWord_132448
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415387712085495581306999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3220516949447327441742665 2415387712085495581306999)
  ·
    refine ⟨3623081568128243371960499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2415387712085495581306999 3623081568128243371960499)
    ·
      refine ⟨5434622352192365057940749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3623081568128243371960499 5434622352192365057940749)
      ·
        refine ⟨2037983382072136896727781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5434622352192365057940749 2037983382072136896727781)
        ·
          refine ⟨382121884138525668136459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2037983382072136896727781 382121884138525668136459)
          ·
            refine ⟨573182826207788502204689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382121884138525668136459 573182826207788502204689)
            ·
              refine ⟨429887119655841376653517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573182826207788502204689 429887119655841376653517)
              ·
                refine ⟨161207669870940516245069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429887119655841376653517 161207669870940516245069)
                ·
                  refine ⟨60452876201602693591901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161207669870940516245069 60452876201602693591901)
                  ·
                    rfl

theorem cell20_132448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_132448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132448 prefixEnd_132448 := by exact prefixLift 132448
  have htrace : WordTrace (prefixWord ++ tailWord_132448) baseStart_132448 baseEnd_132448 := by
    simpa [prefixWord, tailWord_132448, baseEnd_132448] using wordTrace_append hprefix tailTrace_132448
  have hstable : (prefixWord ++ tailWord_132448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132448).length < 2 ^ (prefixWord ++ tailWord_132448).sum := by decide
  have hdescent : baseEnd_132448 < baseStart_132448 := by decide
  rcases family_descends (prefixWord ++ tailWord_132448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132458 : List Nat := [3, 1, 3, 3, 2, 1, 3, 4]
def baseStart_132458 : Nat := 118140960795 + 132458 * 2 ^ 59
def prefixEnd_132458 : Nat := 4983230072969 + 3 ^ 40 * 132458 * 2
def baseEnd_132458 : Nat := 20152480158029034419509

theorem tailTrace_132458 : CollatzResearch.WordTrace tailWord_132458 prefixEnd_132458 20152480158029034419509 := by
  unfold tailWord_132458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1207785038533690717619507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3220760102756508580318685 1207785038533690717619507)
  ·
    refine ⟨1811677557800536076429261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1207785038533690717619507 1811677557800536076429261)
    ·
      refine ⟨679379084175201028660973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1811677557800536076429261 679379084175201028660973)
      ·
        refine ⟨254767156565700385747865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679379084175201028660973 254767156565700385747865)
        ·
          refine ⟨191075367424275289310899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254767156565700385747865 191075367424275289310899)
          ·
            refine ⟨286613051136412933966349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191075367424275289310899 286613051136412933966349)
            ·
              refine ⟨107479894176154850237381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286613051136412933966349 107479894176154850237381)
              ·
                refine ⟨20152480158029034419509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107479894176154850237381 20152480158029034419509)
                ·
                  rfl

theorem cell20_132458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_132458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132458 prefixEnd_132458 := by exact prefixLift 132458
  have htrace : WordTrace (prefixWord ++ tailWord_132458) baseStart_132458 baseEnd_132458 := by
    simpa [prefixWord, tailWord_132458, baseEnd_132458] using wordTrace_append hprefix tailTrace_132458
  have hstable : (prefixWord ++ tailWord_132458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132458).length < 2 ^ (prefixWord ++ tailWord_132458).sum := by decide
  have hdescent : baseEnd_132458 < baseStart_132458 := by decide
  rcases family_descends (prefixWord ++ tailWord_132458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132476 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_132476 : Nat := 118140960795 + 132476 * 2 ^ 59
def prefixEnd_132476 : Nat := 4983230072969 + 3 ^ 40 * 132476 * 2
def baseEnd_132476 : Nat := 60465656164559040658453

theorem tailTrace_132476 : CollatzResearch.WordTrace tailWord_132476 prefixEnd_132476 60465656164559040658453 := by
  unfold tailWord_132476
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415898334034775972316641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3221197778713034629755521 2415898334034775972316641)
  ·
    refine ⟨1811923750526081979237481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2415898334034775972316641 1811923750526081979237481)
    ·
      refine ⟨1358942812894561484428111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1811923750526081979237481 1358942812894561484428111)
      ·
        refine ⟨2038414219341842226642167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1358942812894561484428111 2038414219341842226642167)
        ·
          refine ⟨3057621329012763339963251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2038414219341842226642167 3057621329012763339963251)
          ·
            refine ⟨4586431993519145009944877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3057621329012763339963251 4586431993519145009944877)
            ·
              refine ⟨1719911997569679378729329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4586431993519145009944877 1719911997569679378729329)
              ·
                refine ⟨1289933998177259534046997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719911997569679378729329 1289933998177259534046997)
                ·
                  refine ⟨60465656164559040658453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1289933998177259534046997 60465656164559040658453)
                  ·
                    rfl

theorem cell20_132476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_132476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132476 prefixEnd_132476 := by exact prefixLift 132476
  have htrace : WordTrace (prefixWord ++ tailWord_132476) baseStart_132476 baseEnd_132476 := by
    simpa [prefixWord, tailWord_132476, baseEnd_132476] using wordTrace_append hprefix tailTrace_132476
  have hstable : (prefixWord ++ tailWord_132476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132476).length < 2 ^ (prefixWord ++ tailWord_132476).sum := by decide
  have hdescent : baseEnd_132476 < baseStart_132476 := by decide
  rcases family_descends (prefixWord ++ tailWord_132476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132478 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_132478 : Nat := 118140960795 + 132478 * 2 ^ 59
def prefixEnd_132478 : Nat := 4983230072969 + 3 ^ 40 * 132478 * 2
def baseEnd_132478 : Nat := 60466569019055922591779

theorem tailTrace_132478 : CollatzResearch.WordTrace tailWord_132478 prefixEnd_132478 60466569019055922591779 := by
  unfold tailWord_132478
  simp only [CollatzResearch.WordTrace]
  refine ⟨603983701757788285775761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3221246409374870857470725 603983701757788285775761)
  ·
    refine ⟨452987776318341214331821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 603983701757788285775761 452987776318341214331821)
    ·
      refine ⟨169870416119377955374433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452987776318341214331821 169870416119377955374433)
      ·
        refine ⟨127402812089533466530825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169870416119377955374433 127402812089533466530825)
        ·
          refine ⟨95552109067150099898119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127402812089533466530825 95552109067150099898119)
          ·
            refine ⟨143328163600725149847179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95552109067150099898119 143328163600725149847179)
            ·
              refine ⟨214992245401087724770769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143328163600725149847179 214992245401087724770769)
              ·
                refine ⟨161244184050815793578077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214992245401087724770769 161244184050815793578077)
                ·
                  refine ⟨60466569019055922591779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161244184050815793578077 60466569019055922591779)
                  ·
                    rfl

theorem cell20_132478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_132478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132478 prefixEnd_132478 := by exact prefixLift 132478
  have htrace : WordTrace (prefixWord ++ tailWord_132478) baseStart_132478 baseEnd_132478 := by
    simpa [prefixWord, tailWord_132478, baseEnd_132478] using wordTrace_append hprefix tailTrace_132478
  have hstable : (prefixWord ++ tailWord_132478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132478).length < 2 ^ (prefixWord ++ tailWord_132478).sum := by decide
  have hdescent : baseEnd_132478 < baseStart_132478 := by decide
  rcases family_descends (prefixWord ++ tailWord_132478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132482 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_132482 : Nat := 118140960795 + 132482 * 2 ^ 59
def prefixEnd_132482 : Nat := 4983230072969 + 3 ^ 40 * 132482 * 2
def baseEnd_132482 : Nat := 60468394728049686458429

theorem tailTrace_132482 : CollatzResearch.WordTrace tailWord_132482 prefixEnd_132482 60468394728049686458429 := by
  unfold tailWord_132482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208003876511953742337925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3221343670698543312901133 1208003876511953742337925)
  ·
    refine ⟨226500726845991326688361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1208003876511953742337925 226500726845991326688361)
    ·
      refine ⟨169875545134493495016271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226500726845991326688361 169875545134493495016271)
      ·
        refine ⟨254813317701740242524407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169875545134493495016271 254813317701740242524407)
        ·
          refine ⟨382219976552610363786611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254813317701740242524407 382219976552610363786611)
          ·
            refine ⟨573329964828915545679917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382219976552610363786611 573329964828915545679917)
            ·
              refine ⟨214998736810843329629969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573329964828915545679917 214998736810843329629969)
              ·
                refine ⟨161249052608132497222477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214998736810843329629969 161249052608132497222477)
                ·
                  refine ⟨60468394728049686458429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161249052608132497222477 60468394728049686458429)
                  ·
                    rfl

theorem cell20_132482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_132482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132482 prefixEnd_132482 := by exact prefixLift 132482
  have htrace : WordTrace (prefixWord ++ tailWord_132482) baseStart_132482 baseEnd_132482 := by
    simpa [prefixWord, tailWord_132482, baseEnd_132482] using wordTrace_append hprefix tailTrace_132482
  have hstable : (prefixWord ++ tailWord_132482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132482).length < 2 ^ (prefixWord ++ tailWord_132482).sum := by decide
  have hdescent : baseEnd_132482 < baseStart_132482 := by decide
  rcases family_descends (prefixWord ++ tailWord_132482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132548 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_132548 : Nat := 118140960795 + 132548 * 2 ^ 59
def prefixEnd_132548 : Nat := 4983230072969 + 3 ^ 40 * 132548 * 2
def baseEnd_132548 : Nat := 60498518926446790258159

theorem tailTrace_132548 : CollatzResearch.WordTrace tailWord_132548 prefixEnd_132548 60498518926446790258159 := by
  unfold tailWord_132548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417211361904354120627149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3222948482539138827502865 2417211361904354120627149)
  ·
    refine ⟨906454260714132795235181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2417211361904354120627149 906454260714132795235181)
    ·
      refine ⟨339920347767799798213193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 906454260714132795235181 339920347767799798213193)
      ·
        refine ⟨254940260825849848659895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339920347767799798213193 254940260825849848659895)
        ·
          refine ⟨382410391238774772989843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254940260825849848659895 382410391238774772989843)
          ·
            refine ⟨573615586858162159484765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382410391238774772989843 573615586858162159484765)
            ·
              refine ⟨215105845071810809806787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573615586858162159484765 215105845071810809806787)
              ·
                refine ⟨322658767607716214710181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215105845071810809806787 322658767607716214710181)
                ·
                  refine ⟨60498518926446790258159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322658767607716214710181 60498518926446790258159)
                  ·
                    rfl

theorem cell20_132548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_132548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132548 prefixEnd_132548 := by exact prefixLift 132548
  have htrace : WordTrace (prefixWord ++ tailWord_132548) baseStart_132548 baseEnd_132548 := by
    simpa [prefixWord, tailWord_132548, baseEnd_132548] using wordTrace_append hprefix tailTrace_132548
  have hstable : (prefixWord ++ tailWord_132548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132548).length < 2 ^ (prefixWord ++ tailWord_132548).sum := by decide
  have hdescent : baseEnd_132548 < baseStart_132548 := by decide
  rcases family_descends (prefixWord ++ tailWord_132548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132559 : List Nat := [1, 1, 2, 1, 1, 4, 3, 7]
def baseStart_132559 : Nat := 118140960795 + 132559 * 2 ^ 59
def prefixEnd_132559 : Nat := 4983230072969 + 3 ^ 40 * 132559 * 2
def baseEnd_132559 : Nat := 20167846542059880297149

theorem tailTrace_132559 : CollatzResearch.WordTrace tailWord_132559 prefixEnd_132559 20167846542059880297149 := by
  unfold tailWord_132559
  simp only [CollatzResearch.WordTrace]
  refine ⟨4834823926768857119904731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3223215951179238079936487 4834823926768857119904731)
  ·
    refine ⟨7252235890153285679857097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4834823926768857119904731 7252235890153285679857097)
    ·
      refine ⟨5439176917614964259892823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7252235890153285679857097 5439176917614964259892823)
      ·
        refine ⟨8158765376422446389839235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5439176917614964259892823 8158765376422446389839235)
        ·
          refine ⟨12238148064633669584758853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8158765376422446389839235 12238148064633669584758853)
          ·
            refine ⟨2294652762118813047142285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12238148064633669584758853 2294652762118813047142285)
            ·
              refine ⟨860494785794554892678357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2294652762118813047142285 860494785794554892678357)
              ·
                refine ⟨20167846542059880297149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 860494785794554892678357 20167846542059880297149)
                ·
                  rfl

theorem cell20_132559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_132559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132559 prefixEnd_132559 := by exact prefixLift 132559
  have htrace : WordTrace (prefixWord ++ tailWord_132559) baseStart_132559 baseEnd_132559 := by
    simpa [prefixWord, tailWord_132559, baseEnd_132559] using wordTrace_append hprefix tailTrace_132559
  have hstable : (prefixWord ++ tailWord_132559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132559).length < 2 ^ (prefixWord ++ tailWord_132559).sum := by decide
  have hdescent : baseEnd_132559 < baseStart_132559 := by decide
  rcases family_descends (prefixWord ++ tailWord_132559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132600 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_132600 : Nat := 118140960795 + 132600 * 2 ^ 59
def prefixEnd_132600 : Nat := 4983230072969 + 3 ^ 40 * 132600 * 2
def baseEnd_132600 : Nat := 60522253143365720524613

theorem tailTrace_132600 : CollatzResearch.WordTrace tailWord_132600 prefixEnd_132600 60522253143365720524613 := by
  unfold tailWord_132600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418159659810160561073627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3224212879746880748098169 2418159659810160561073627)
  ·
    refine ⟨3627239489715240841610441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2418159659810160561073627 3627239489715240841610441)
    ·
      refine ⟨2720429617286430631207831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3627239489715240841610441 2720429617286430631207831)
      ·
        refine ⟨4080644425929645946811747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720429617286430631207831 4080644425929645946811747)
        ·
          refine ⟨6120966638894468920217621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4080644425929645946811747 6120966638894468920217621)
          ·
            refine ⟨286920311198178230635201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6120966638894468920217621 286920311198178230635201)
            ·
              refine ⟨215190233398633672976401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286920311198178230635201 215190233398633672976401)
              ·
                refine ⟨161392675048975254732301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215190233398633672976401 161392675048975254732301)
                ·
                  refine ⟨60522253143365720524613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161392675048975254732301 60522253143365720524613)
                  ·
                    rfl

theorem cell20_132600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_132600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132600 prefixEnd_132600 := by exact prefixLift 132600
  have htrace : WordTrace (prefixWord ++ tailWord_132600) baseStart_132600 baseEnd_132600 := by
    simpa [prefixWord, tailWord_132600, baseEnd_132600] using wordTrace_append hprefix tailTrace_132600
  have hstable : (prefixWord ++ tailWord_132600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132600).length < 2 ^ (prefixWord ++ tailWord_132600).sum := by decide
  have hdescent : baseEnd_132600 < baseStart_132600 := by decide
  rcases family_descends (prefixWord ++ tailWord_132600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132610 : List Nat := [3, 4, 1, 2, 1, 3, 1, 5]
def baseStart_132610 : Nat := 118140960795 + 132610 * 2 ^ 59
def prefixEnd_132610 : Nat := 4983230072969 + 3 ^ 40 * 132610 * 2
def baseEnd_132610 : Nat := 20175605805283376730413

theorem tailTrace_132610 : CollatzResearch.WordTrace tailWord_132610 prefixEnd_132610 20175605805283376730413 := by
  unfold tailWord_132610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209171012396023207502821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3224456033056061886674189 1209171012396023207502821)
  ·
    refine ⟨226719564824254351406779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1209171012396023207502821 226719564824254351406779)
    ·
      refine ⟨340079347236381527110169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226719564824254351406779 340079347236381527110169)
      ·
        refine ⟨255059510427286145332627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340079347236381527110169 255059510427286145332627)
        ·
          refine ⟨382589265640929217998941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255059510427286145332627 382589265640929217998941)
          ·
            refine ⟨143470974615348456749603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382589265640929217998941 143470974615348456749603)
            ·
              refine ⟨215206461923022685124405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143470974615348456749603 215206461923022685124405)
              ·
                refine ⟨20175605805283376730413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215206461923022685124405 20175605805283376730413)
                ·
                  rfl

theorem cell20_132610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_132610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132610 prefixEnd_132610 := by exact prefixLift 132610
  have htrace : WordTrace (prefixWord ++ tailWord_132610) baseStart_132610 baseEnd_132610 := by
    simpa [prefixWord, tailWord_132610, baseEnd_132610] using wordTrace_append hprefix tailTrace_132610
  have hstable : (prefixWord ++ tailWord_132610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132610).length < 2 ^ (prefixWord ++ tailWord_132610).sum := by decide
  have hdescent : baseEnd_132610 < baseStart_132610 := by decide
  rcases family_descends (prefixWord ++ tailWord_132610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132659 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 5]
def baseStart_132659 : Nat := 118140960795 + 132659 * 2 ^ 59
def prefixEnd_132659 : Nat := 4983230072969 + 3 ^ 40 * 132659 * 2
def baseEnd_132659 : Nat := 60549182351023737557705

theorem tailTrace_132659 : CollatzResearch.WordTrace tailWord_132659 prefixEnd_132659 60549182351023737557705 := by
  unfold tailWord_132659
  simp only [CollatzResearch.WordTrace]
  refine ⟨4838471226406574198545031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3225647484271049465696687 4838471226406574198545031)
  ·
    refine ⟨7257706839609861297817547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4838471226406574198545031 7257706839609861297817547)
    ·
      refine ⟨10886560259414791946726321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7257706839609861297817547 10886560259414791946726321)
      ·
        refine ⟨8164920194561093960044741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10886560259414791946726321 8164920194561093960044741)
        ·
          refine ⟨1530922536480205117508389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8164920194561093960044741 1530922536480205117508389)
          ·
            refine ⟨287047975590038459532823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1530922536480205117508389 287047975590038459532823)
            ·
              refine ⟨430571963385057689299235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287047975590038459532823 430571963385057689299235)
              ·
                refine ⟨645857945077586533948853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430571963385057689299235 645857945077586533948853)
                ·
                  refine ⟨60549182351023737557705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 645857945077586533948853 60549182351023737557705)
                  ·
                    rfl

theorem cell20_132659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_132659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132659 prefixEnd_132659 := by exact prefixLift 132659
  have htrace : WordTrace (prefixWord ++ tailWord_132659) baseStart_132659 baseEnd_132659 := by
    simpa [prefixWord, tailWord_132659, baseEnd_132659] using wordTrace_append hprefix tailTrace_132659
  have hstable : (prefixWord ++ tailWord_132659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132659).length < 2 ^ (prefixWord ++ tailWord_132659).sum := by decide
  have hdescent : baseEnd_132659 < baseStart_132659 := by decide
  rcases family_descends (prefixWord ++ tailWord_132659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132690 : List Nat := [3, 2, 2, 1, 2, 3, 1, 6]
def baseStart_132690 : Nat := 118140960795 + 132690 * 2 ^ 59
def prefixEnd_132690 : Nat := 4983230072969 + 3 ^ 40 * 132690 * 2
def baseEnd_132690 : Nat := 20187777198575135841415

theorem tailTrace_132690 : CollatzResearch.WordTrace tailWord_132690 prefixEnd_132690 20187777198575135841415 := by
  unfold tailWord_132690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209900472323566623230881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3226401259529510995282349 1209900472323566623230881)
  ·
    refine ⟨907425354242674967423161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1209900472323566623230881 907425354242674967423161)
    ·
      refine ⟨680569015682006225567371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 907425354242674967423161 680569015682006225567371)
      ·
        refine ⟨1020853523523009338351057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680569015682006225567371 1020853523523009338351057)
        ·
          refine ⟨765640142642257003763293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020853523523009338351057 765640142642257003763293)
          ·
            refine ⟨287115053490846376411235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765640142642257003763293 287115053490846376411235)
            ·
              refine ⟨430672580236269564616853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287115053490846376411235 430672580236269564616853)
              ·
                refine ⟨20187777198575135841415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430672580236269564616853 20187777198575135841415)
                ·
                  rfl

theorem cell20_132690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_132690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132690 prefixEnd_132690 := by exact prefixLift 132690
  have htrace : WordTrace (prefixWord ++ tailWord_132690) baseStart_132690 baseEnd_132690 := by
    simpa [prefixWord, tailWord_132690, baseEnd_132690] using wordTrace_append hprefix tailTrace_132690
  have hstable : (prefixWord ++ tailWord_132690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132690).length < 2 ^ (prefixWord ++ tailWord_132690).sum := by decide
  have hdescent : baseEnd_132690 < baseStart_132690 := by decide
  rcases family_descends (prefixWord ++ tailWord_132690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132711 : List Nat := [1, 1, 5, 1, 1, 1, 10]
def baseStart_132711 : Nat := 118140960795 + 132711 * 2 ^ 59
def prefixEnd_132711 : Nat := 4983230072969 + 3 ^ 40 * 132711 * 2
def baseEnd_132711 : Nat := 6730324063104740869351

theorem tailTrace_132711 : CollatzResearch.WordTrace tailWord_132711 prefixEnd_132711 6730324063104740869351 := by
  unfold tailWord_132711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4840367822218187079437987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3226911881478791386291991 4840367822218187079437987)
  ·
    refine ⟨7260551733327280619156981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4840367822218187079437987 7260551733327280619156981)
    ·
      refine ⟨680676724999432558045967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7260551733327280619156981 680676724999432558045967)
      ·
        refine ⟨1021015087499148837068951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680676724999432558045967 1021015087499148837068951)
        ·
          refine ⟨1531522631248723255603427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021015087499148837068951 1531522631248723255603427)
          ·
            refine ⟨2297283946873084883405141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531522631248723255603427 2297283946873084883405141)
            ·
              refine ⟨6730324063104740869351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2297283946873084883405141 6730324063104740869351)
              ·
                rfl

theorem cell20_132711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 10].length) (baseStart_132711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132711 prefixEnd_132711 := by exact prefixLift 132711
  have htrace : WordTrace (prefixWord ++ tailWord_132711) baseStart_132711 baseEnd_132711 := by
    simpa [prefixWord, tailWord_132711, baseEnd_132711] using wordTrace_append hprefix tailTrace_132711
  have hstable : (prefixWord ++ tailWord_132711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132711).length < 2 ^ (prefixWord ++ tailWord_132711).sum := by decide
  have hdescent : baseEnd_132711 < baseStart_132711 := by decide
  rcases family_descends (prefixWord ++ tailWord_132711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132717 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 4]
def baseStart_132717 : Nat := 118140960795 + 132717 * 2 ^ 59
def prefixEnd_132717 : Nat := 4983230072969 + 3 ^ 40 * 132717 * 2
def baseEnd_132717 : Nat := 60575655131433313624135

theorem tailTrace_132717 : CollatzResearch.WordTrace tailWord_132717 prefixEnd_132717 60575655131433313624135 := by
  unfold tailWord_132717
  simp only [CollatzResearch.WordTrace]
  refine ⟨4840586660196450104156405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3227057773464300069437603 4840586660196450104156405)
  ·
    refine ⟨453804999393417197264663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4840586660196450104156405 453804999393417197264663)
    ·
      refine ⟨680707499090125795896995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453804999393417197264663 680707499090125795896995)
      ·
        refine ⟨1021061248635188693845493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680707499090125795896995 1021061248635188693845493)
        ·
          refine ⟨95724492059548940048015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1021061248635188693845493 95724492059548940048015)
          ·
            refine ⟨143586738089323410072023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95724492059548940048015 143586738089323410072023)
            ·
              refine ⟨215380107133985115108035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143586738089323410072023 215380107133985115108035)
              ·
                refine ⟨323070160700977672662053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215380107133985115108035 323070160700977672662053)
                ·
                  refine ⟨60575655131433313624135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 323070160700977672662053 60575655131433313624135)
                  ·
                    rfl

theorem cell20_132717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_132717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132717 prefixEnd_132717 := by exact prefixLift 132717
  have htrace : WordTrace (prefixWord ++ tailWord_132717) baseStart_132717 baseEnd_132717 := by
    simpa [prefixWord, tailWord_132717, baseEnd_132717] using wordTrace_append hprefix tailTrace_132717
  have hstable : (prefixWord ++ tailWord_132717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132717).length < 2 ^ (prefixWord ++ tailWord_132717).sum := by decide
  have hdescent : baseEnd_132717 < baseStart_132717 := by decide
  rcases family_descends (prefixWord ++ tailWord_132717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132721 : List Nat := [1, 2, 2, 2, 1, 1, 1, 8, 2]
def baseStart_132721 : Nat := 118140960795 + 132721 * 2 ^ 59
def prefixEnd_132721 : Nat := 4983230072969 + 3 ^ 40 * 132721 * 2
def baseEnd_132721 : Nat := 60577480840427077490785

theorem tailTrace_132721 : CollatzResearch.WordTrace tailWord_132721 prefixEnd_132721 60577480840427077490785 := by
  unfold tailWord_132721
  simp only [CollatzResearch.WordTrace]
  refine ⟨4840732552181958787302017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3227155034787972524868011 4840732552181958787302017)
  ·
    refine ⟨3630549414136469090476513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4840732552181958787302017 3630549414136469090476513)
    ·
      refine ⟨2722912060602351817857385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3630549414136469090476513 2722912060602351817857385)
      ·
        refine ⟨2042184045451763863393039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2722912060602351817857385 2042184045451763863393039)
        ·
          refine ⟨3063276068177645795089559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042184045451763863393039 3063276068177645795089559)
          ·
            refine ⟨4594914102266468692634339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063276068177645795089559 4594914102266468692634339)
            ·
              refine ⟨6892371153399703038951509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594914102266468692634339 6892371153399703038951509)
              ·
                refine ⟨80769974453902769987713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6892371153399703038951509 80769974453902769987713)
                ·
                  refine ⟨60577480840427077490785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80769974453902769987713 60577480840427077490785)
                  ·
                    rfl

theorem cell20_132721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_132721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132721 prefixEnd_132721 := by exact prefixLift 132721
  have htrace : WordTrace (prefixWord ++ tailWord_132721) baseStart_132721 baseEnd_132721 := by
    simpa [prefixWord, tailWord_132721, baseEnd_132721] using wordTrace_append hprefix tailTrace_132721
  have hstable : (prefixWord ++ tailWord_132721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132721).length < 2 ^ (prefixWord ++ tailWord_132721).sum := by decide
  have hdescent : baseEnd_132721 < baseStart_132721 := by decide
  rcases family_descends (prefixWord ++ tailWord_132721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132766 : List Nat := [4, 3, 1, 1, 1, 10]
def baseStart_132766 : Nat := 118140960795 + 132766 * 2 ^ 59
def prefixEnd_132766 : Nat := 4983230072969 + 3 ^ 40 * 132766 * 2
def baseEnd_132766 : Nat := 2244371113578034110763

theorem tailTrace_132766 : CollatzResearch.WordTrace tailWord_132766 prefixEnd_132766 2244371113578034110763 := by
  unfold tailWord_132766
  simp only [CollatzResearch.WordTrace]
  refine ⟨605296729627366434086269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3228249224679287648460101 605296729627366434086269)
  ·
    refine ⟨226986273610262412782351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 605296729627366434086269 226986273610262412782351)
    ·
      refine ⟨340479410415393619173527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226986273610262412782351 340479410415393619173527)
      ·
        refine ⟨510719115623090428760291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340479410415393619173527 510719115623090428760291)
        ·
          refine ⟨766078673434635643140437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510719115623090428760291 766078673434635643140437)
          ·
            refine ⟨2244371113578034110763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 766078673434635643140437 2244371113578034110763)
            ·
              rfl

theorem cell20_132766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 10].length) (baseStart_132766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132766 prefixEnd_132766 := by exact prefixLift 132766
  have htrace : WordTrace (prefixWord ++ tailWord_132766) baseStart_132766 baseEnd_132766 := by
    simpa [prefixWord, tailWord_132766, baseEnd_132766] using wordTrace_append hprefix tailTrace_132766
  have hstable : (prefixWord ++ tailWord_132766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132766).length < 2 ^ (prefixWord ++ tailWord_132766).sum := by decide
  have hdescent : baseEnd_132766 < baseStart_132766 := by decide
  rcases family_descends (prefixWord ++ tailWord_132766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132773 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 3]
def baseStart_132773 : Nat := 118140960795 + 132773 * 2 ^ 59
def prefixEnd_132773 : Nat := 4983230072969 + 3 ^ 40 * 132773 * 2
def baseEnd_132773 : Nat := 60601215057346007757239

theorem tailTrace_132773 : CollatzResearch.WordTrace tailWord_132773 prefixEnd_132773 60601215057346007757239 := by
  unfold tailWord_132773
  simp only [CollatzResearch.WordTrace]
  refine ⟨4842629147993571668194973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3228419431995714445463315 4842629147993571668194973)
  ·
    refine ⟨1815985930497589375573115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4842629147993571668194973 1815985930497589375573115)
    ·
      refine ⟨2723978895746384063359673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1815985930497589375573115 2723978895746384063359673)
      ·
        refine ⟨2042984171809788047519755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2723978895746384063359673 2042984171809788047519755)
        ·
          refine ⟨3064476257714682071279633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042984171809788047519755 3064476257714682071279633)
          ·
            refine ⟨2298357193286011553459725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3064476257714682071279633 2298357193286011553459725)
            ·
              refine ⟨861883947482254332547397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2298357193286011553459725 861883947482254332547397)
              ·
                refine ⟨161603240152922687352637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 861883947482254332547397 161603240152922687352637)
                ·
                  refine ⟨60601215057346007757239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161603240152922687352637 60601215057346007757239)
                  ·
                    rfl

theorem cell20_132773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_132773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132773 prefixEnd_132773 := by exact prefixLift 132773
  have htrace : WordTrace (prefixWord ++ tailWord_132773) baseStart_132773 baseEnd_132773 := by
    simpa [prefixWord, tailWord_132773, baseEnd_132773] using wordTrace_append hprefix tailTrace_132773
  have hstable : (prefixWord ++ tailWord_132773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132773).length < 2 ^ (prefixWord ++ tailWord_132773).sum := by decide
  have hdescent : baseEnd_132773 < baseStart_132773 := by decide
  rcases family_descends (prefixWord ++ tailWord_132773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132814 : List Nat := [4, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_132814 : Nat := 118140960795 + 132814 * 2 ^ 59
def prefixEnd_132814 : Nat := 4983230072969 + 3 ^ 40 * 132814 * 2
def baseEnd_132814 : Nat := 60619928574532087390405

theorem tailTrace_132814 : CollatzResearch.WordTrace tailWord_132814 prefixEnd_132814 60619928574532087390405 := by
  unfold tailWord_132814
  simp only [CollatzResearch.WordTrace]
  refine ⟨605515567605629458804687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3229416360563357113624997 605515567605629458804687)
  ·
    refine ⟨908273351408444188207031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 605515567605629458804687 908273351408444188207031)
    ·
      refine ⟨1362410027112666282310547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 908273351408444188207031 1362410027112666282310547)
      ·
        refine ⟨2043615040668999423465821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362410027112666282310547 2043615040668999423465821)
        ·
          refine ⟨766355640250874783799683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2043615040668999423465821 766355640250874783799683)
          ·
            refine ⟨1149533460376312175699525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766355640250874783799683 1149533460376312175699525)
            ·
              refine ⟨215537523820558532943661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1149533460376312175699525 215537523820558532943661)
              ·
                refine ⟨80826571432709449853873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215537523820558532943661 80826571432709449853873)
                ·
                  refine ⟨60619928574532087390405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80826571432709449853873 60619928574532087390405)
                  ·
                    rfl

theorem cell20_132814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_132814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132814 prefixEnd_132814 := by exact prefixLift 132814
  have htrace : WordTrace (prefixWord ++ tailWord_132814) baseStart_132814 baseEnd_132814 := by
    simpa [prefixWord, tailWord_132814, baseEnd_132814] using wordTrace_append hprefix tailTrace_132814
  have hstable : (prefixWord ++ tailWord_132814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132814).length < 2 ^ (prefixWord ++ tailWord_132814).sum := by decide
  have hdescent : baseEnd_132814 < baseStart_132814 := by decide
  rcases family_descends (prefixWord ++ tailWord_132814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132825 : List Nat := [1, 2, 1, 2, 3, 4, 7]
def baseStart_132825 : Nat := 118140960795 + 132825 * 2 ^ 59
def prefixEnd_132825 : Nat := 4983230072969 + 3 ^ 40 * 132825 * 2
def baseEnd_132825 : Nat := 6736105474918326447077

theorem tailTrace_132825 : CollatzResearch.WordTrace tailWord_132825 prefixEnd_132825 6736105474918326447077 := by
  unfold tailWord_132825
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844525743805184549087929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3229683829203456366058619 4844525743805184549087929)
  ·
    refine ⟨3633394307853888411815947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4844525743805184549087929 3633394307853888411815947)
    ·
      refine ⟨5450091461780832617723921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3633394307853888411815947 5450091461780832617723921)
      ·
        refine ⟨4087568596335624463292941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5450091461780832617723921 4087568596335624463292941)
        ·
          refine ⟨1532838223625859173734853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4087568596335624463292941 1532838223625859173734853)
          ·
            refine ⟨287407166929848595075285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1532838223625859173734853 287407166929848595075285)
            ·
              refine ⟨6736105474918326447077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 287407166929848595075285 6736105474918326447077)
              ·
                rfl

theorem cell20_132825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 7].length) (baseStart_132825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132825 prefixEnd_132825 := by exact prefixLift 132825
  have htrace : WordTrace (prefixWord ++ tailWord_132825) baseStart_132825 baseEnd_132825 := by
    simpa [prefixWord, tailWord_132825, baseEnd_132825] using wordTrace_append hprefix tailTrace_132825
  have hstable : (prefixWord ++ tailWord_132825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132825).length < 2 ^ (prefixWord ++ tailWord_132825).sum := by decide
  have hdescent : baseEnd_132825 < baseStart_132825 := by decide
  rcases family_descends (prefixWord ++ tailWord_132825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132845 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 3]
def baseStart_132845 : Nat := 118140960795 + 132845 * 2 ^ 59
def prefixEnd_132845 : Nat := 4983230072969 + 3 ^ 40 * 132845 * 2
def baseEnd_132845 : Nat := 60634077819233757356945

theorem tailTrace_132845 : CollatzResearch.WordTrace tailWord_132845 prefixEnd_132845 60634077819233757356945 := by
  unfold tailWord_132845
  simp only [CollatzResearch.WordTrace]
  refine ⟨4845255203732727964815989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3230170135821818643210659 4845255203732727964815989)
  ·
    refine ⟨454242675349943246701499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4845255203732727964815989 454242675349943246701499)
    ·
      refine ⟨681364013024914870052249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454242675349943246701499 681364013024914870052249)
      ·
        refine ⟨511023009768686152539187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681364013024914870052249 511023009768686152539187)
        ·
          refine ⟨766534514653029228808781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511023009768686152539187 766534514653029228808781)
          ·
            refine ⟨287450442994885960803293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 766534514653029228808781 287450442994885960803293)
            ·
              refine ⟨107793916123082235301235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287450442994885960803293 107793916123082235301235)
              ·
                refine ⟨161690874184623352951853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107793916123082235301235 161690874184623352951853)
                ·
                  refine ⟨60634077819233757356945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161690874184623352951853 60634077819233757356945)
                  ·
                    rfl

theorem cell20_132845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_132845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132845 prefixEnd_132845 := by exact prefixLift 132845
  have htrace : WordTrace (prefixWord ++ tailWord_132845) baseStart_132845 baseEnd_132845 := by
    simpa [prefixWord, tailWord_132845, baseEnd_132845] using wordTrace_append hprefix tailTrace_132845
  have hstable : (prefixWord ++ tailWord_132845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132845).length < 2 ^ (prefixWord ++ tailWord_132845).sum := by decide
  have hdescent : baseEnd_132845 < baseStart_132845 := by decide
  rcases family_descends (prefixWord ++ tailWord_132845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132887 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_132887 : Nat := 118140960795 + 132887 * 2 ^ 59
def prefixEnd_132887 : Nat := 4983230072969 + 3 ^ 40 * 132887 * 2
def baseEnd_132887 : Nat := 60653247763668277956773

theorem tailTrace_132887 : CollatzResearch.WordTrace tailWord_132887 prefixEnd_132887 60653247763668277956773 := by
  unfold tailWord_132887
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846787069580569137844915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3231191379720379425229943 4846787069580569137844915)
  ·
    refine ⟨7270180604370853706767373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4846787069580569137844915 7270180604370853706767373)
    ·
      refine ⟨2726317726639070140037765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7270180604370853706767373 2726317726639070140037765)
      ·
        refine ⟨511184573744825651257081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2726317726639070140037765 511184573744825651257081)
        ·
          refine ⟨383388430308619238442811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 511184573744825651257081 383388430308619238442811)
          ·
            refine ⟨575082645462928857664217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383388430308619238442811 575082645462928857664217)
            ·
              refine ⟨431311984097196643248163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575082645462928857664217 431311984097196643248163)
              ·
                refine ⟨646967976145794964872245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431311984097196643248163 646967976145794964872245)
                ·
                  refine ⟨60653247763668277956773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 646967976145794964872245 60653247763668277956773)
                  ·
                    rfl

theorem cell20_132887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_132887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132887 prefixEnd_132887 := by exact prefixLift 132887
  have htrace : WordTrace (prefixWord ++ tailWord_132887) baseStart_132887 baseEnd_132887 := by
    simpa [prefixWord, tailWord_132887, baseEnd_132887] using wordTrace_append hprefix tailTrace_132887
  have hstable : (prefixWord ++ tailWord_132887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132887).length < 2 ^ (prefixWord ++ tailWord_132887).sum := by decide
  have hdescent : baseEnd_132887 < baseStart_132887 := by decide
  rcases family_descends (prefixWord ++ tailWord_132887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132901 : List Nat := [1, 3, 1, 2, 3, 2, 1, 7]
def baseStart_132901 : Nat := 118140960795 + 132901 * 2 ^ 59
def prefixEnd_132901 : Nat := 4983230072969 + 3 ^ 40 * 132901 * 2
def baseEnd_132901 : Nat := 20219879248382150496683

theorem tailTrace_132901 : CollatzResearch.WordTrace tailWord_132901 prefixEnd_132901 20219879248382150496683 := by
  unfold tailWord_132901
  simp only [CollatzResearch.WordTrace]
  refine ⟨4847297691529849528854557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3231531794353233019236371 4847297691529849528854557)
  ·
    refine ⟨1817736634323693573320459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4847297691529849528854557 1817736634323693573320459)
    ·
      refine ⟨2726604951485540359980689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1817736634323693573320459 2726604951485540359980689)
      ·
        refine ⟨2044953713614155269985517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2726604951485540359980689 2044953713614155269985517)
        ·
          refine ⟨766857642605308226244569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2044953713614155269985517 766857642605308226244569)
          ·
            refine ⟨575143231953981169683427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766857642605308226244569 575143231953981169683427)
            ·
              refine ⟨862714847930971754525141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575143231953981169683427 862714847930971754525141)
              ·
                refine ⟨20219879248382150496683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 862714847930971754525141 20219879248382150496683)
                ·
                  rfl

theorem cell20_132901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_132901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132901 prefixEnd_132901 := by exact prefixLift 132901
  have htrace : WordTrace (prefixWord ++ tailWord_132901) baseStart_132901 baseEnd_132901 := by
    simpa [prefixWord, tailWord_132901, baseEnd_132901] using wordTrace_append hprefix tailTrace_132901
  have hstable : (prefixWord ++ tailWord_132901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132901).length < 2 ^ (prefixWord ++ tailWord_132901).sum := by decide
  have hdescent : baseEnd_132901 < baseStart_132901 := by decide
  rcases family_descends (prefixWord ++ tailWord_132901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132904 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_132904 : Nat := 118140960795 + 132904 * 2 ^ 59
def prefixEnd_132904 : Nat := 4983230072969 + 3 ^ 40 * 132904 * 2
def baseEnd_132904 : Nat := 60661007026891774390037

theorem tailTrace_132904 : CollatzResearch.WordTrace tailWord_132904 prefixEnd_132904 60661007026891774390037 := by
  unfold tailWord_132904
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423703555259490520606883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3231604740345987360809177 2423703555259490520606883)
  ·
    refine ⟨3635555332889235780910325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2423703555259490520606883 3635555332889235780910325)
    ·
      refine ⟨340833312458365854460343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3635555332889235780910325 340833312458365854460343)
      ·
        refine ⟨511249968687548781690515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340833312458365854460343 511249968687548781690515)
        ·
          refine ⟨766874953031323172535773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511249968687548781690515 766874953031323172535773)
          ·
            refine ⟨287578107386746189700915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 766874953031323172535773 287578107386746189700915)
            ·
              refine ⟨431367161080119284551373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287578107386746189700915 431367161080119284551373)
              ·
                refine ⟨161762685405044731706765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431367161080119284551373 161762685405044731706765)
                ·
                  refine ⟨60661007026891774390037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161762685405044731706765 60661007026891774390037)
                  ·
                    rfl

theorem cell20_132904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_132904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132904 prefixEnd_132904 := by exact prefixLift 132904
  have htrace : WordTrace (prefixWord ++ tailWord_132904) baseStart_132904 baseEnd_132904 := by
    simpa [prefixWord, tailWord_132904, baseEnd_132904] using wordTrace_append hprefix tailTrace_132904
  have hstable : (prefixWord ++ tailWord_132904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132904).length < 2 ^ (prefixWord ++ tailWord_132904).sum := by decide
  have hdescent : baseEnd_132904 < baseStart_132904 := by decide
  rcases family_descends (prefixWord ++ tailWord_132904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132945 : List Nat := [1, 2, 2, 1, 5, 3, 2, 2, 2]
def baseStart_132945 : Nat := 118140960795 + 132945 * 2 ^ 59
def prefixEnd_132945 : Nat := 4983230072969 + 3 ^ 40 * 132945 * 2
def baseEnd_132945 : Nat := 60679720544077854023203

theorem tailTrace_132945 : CollatzResearch.WordTrace tailWord_132945 prefixEnd_132945 60679720544077854023203 := by
  unfold tailWord_132945
  simp only [CollatzResearch.WordTrace]
  refine ⟨4848902503370445043456289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3232601668913630028970859 4848902503370445043456289)
  ·
    refine ⟨3636676877527833782592217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4848902503370445043456289 3636676877527833782592217)
    ·
      refine ⟨2727507658145875336944163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3636676877527833782592217 2727507658145875336944163)
      ·
        refine ⟨4091261487218813005416245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727507658145875336944163 4091261487218813005416245)
        ·
          refine ⟨383555764426763719257773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4091261487218813005416245 383555764426763719257773)
          ·
            refine ⟨143833411660036394721665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 383555764426763719257773 143833411660036394721665)
            ·
              refine ⟨107875058745027296041249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143833411660036394721665 107875058745027296041249)
              ·
                refine ⟨80906294058770472030937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107875058745027296041249 80906294058770472030937)
                ·
                  refine ⟨60679720544077854023203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80906294058770472030937 60679720544077854023203)
                  ·
                    rfl

theorem cell20_132945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_132945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132945 prefixEnd_132945 := by exact prefixLift 132945
  have htrace : WordTrace (prefixWord ++ tailWord_132945) baseStart_132945 baseEnd_132945 := by
    simpa [prefixWord, tailWord_132945, baseEnd_132945] using wordTrace_append hprefix tailTrace_132945
  have hstable : (prefixWord ++ tailWord_132945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132945).length < 2 ^ (prefixWord ++ tailWord_132945).sum := by decide
  have hdescent : baseEnd_132945 < baseStart_132945 := by decide
  rcases family_descends (prefixWord ++ tailWord_132945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132991 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_132991 : Nat := 118140960795 + 132991 * 2 ^ 59
def prefixEnd_132991 : Nat := 4983230072969 + 3 ^ 40 * 132991 * 2
def baseEnd_132991 : Nat := 60700716197506138489681

theorem tailTrace_132991 : CollatzResearch.WordTrace tailWord_132991 prefixEnd_132991 60700716197506138489681 := by
  unfold tailWord_132991
  simp only [CollatzResearch.WordTrace]
  refine ⟨4850580261203794899630827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3233720174135863266420551 4850580261203794899630827)
  ·
    refine ⟨7275870391805692349446241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4850580261203794899630827 7275870391805692349446241)
    ·
      refine ⟨5456902793854269262084681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7275870391805692349446241 5456902793854269262084681)
      ·
        refine ⟨4092677095390701946563511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5456902793854269262084681 4092677095390701946563511)
        ·
          refine ⟨6139015643086052919845267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4092677095390701946563511 6139015643086052919845267)
          ·
            refine ⟨9208523464629079379767901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6139015643086052919845267 9208523464629079379767901)
            ·
              refine ⟨3453196299235904767412963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9208523464629079379767901 3453196299235904767412963)
              ·
                refine ⟨5179794448853857151119445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3453196299235904767412963 5179794448853857151119445)
                ·
                  refine ⟨60700716197506138489681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5179794448853857151119445 60700716197506138489681)
                  ·
                    rfl

theorem cell20_132991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_132991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_132991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_132991 prefixEnd_132991 := by exact prefixLift 132991
  have htrace : WordTrace (prefixWord ++ tailWord_132991) baseStart_132991 baseEnd_132991 := by
    simpa [prefixWord, tailWord_132991, baseEnd_132991] using wordTrace_append hprefix tailTrace_132991
  have hstable : (prefixWord ++ tailWord_132991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132991).length < 2 ^ (prefixWord ++ tailWord_132991).sum := by decide
  have hdescent : baseEnd_132991 < baseStart_132991 := by decide
  rcases family_descends (prefixWord ++ tailWord_132991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133053 : List Nat := [1, 4, 1, 2, 3, 1, 8]
def baseStart_133053 : Nat := 118140960795 + 133053 * 2 ^ 59
def prefixEnd_133053 : Nat := 4983230072969 + 3 ^ 40 * 133053 * 2
def baseEnd_133053 : Nat := 6747668298545497602529

theorem tailTrace_133053 : CollatzResearch.WordTrace tailWord_133053 prefixEnd_133053 6747668298545497602529 := by
  unfold tailWord_133053
  simp only [CollatzResearch.WordTrace]
  refine ⟨4852841586979179488387813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3235227724652786325591875 4852841586979179488387813)
  ·
    refine ⟨909907797558596154072715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4852841586979179488387813 909907797558596154072715)
    ·
      refine ⟨1364861696337894231109073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 909907797558596154072715 1364861696337894231109073)
      ·
        refine ⟨1023646272253420673331805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1364861696337894231109073 1023646272253420673331805)
        ·
          refine ⟨383867352095032752499427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1023646272253420673331805 383867352095032752499427)
          ·
            refine ⟨575801028142549128749141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383867352095032752499427 575801028142549128749141)
            ·
              refine ⟨6747668298545497602529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 575801028142549128749141 6747668298545497602529)
              ·
                rfl

theorem cell20_133053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 8].length) (baseStart_133053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133053 prefixEnd_133053 := by exact prefixLift 133053
  have htrace : WordTrace (prefixWord ++ tailWord_133053) baseStart_133053 baseEnd_133053 := by
    simpa [prefixWord, tailWord_133053, baseEnd_133053] using wordTrace_append hprefix tailTrace_133053
  have hstable : (prefixWord ++ tailWord_133053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133053).length < 2 ^ (prefixWord ++ tailWord_133053).sum := by decide
  have hdescent : baseEnd_133053 < baseStart_133053 := by decide
  rcases family_descends (prefixWord ++ tailWord_133053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133091 : List Nat := [1, 1, 1, 6, 1, 2, 2, 6]
def baseStart_133091 : Nat := 118140960795 + 133091 * 2 ^ 59
def prefixEnd_133091 : Nat := 4983230072969 + 3 ^ 40 * 133091 * 2
def baseEnd_133091 : Nat := 20248786307450078385313

theorem tailTrace_133091 : CollatzResearch.WordTrace tailWord_133091 prefixEnd_133091 20248786307450078385313 := by
  unfold tailWord_133091
  simp only [CollatzResearch.WordTrace]
  refine ⟨4854227560841511978271127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3236151707227674652180751 4854227560841511978271127)
  ·
    refine ⟨7281341341262267967406691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4854227560841511978271127 7281341341262267967406691)
    ·
      refine ⟨10922012011893401951110037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7281341341262267967406691 10922012011893401951110037)
      ·
        refine ⟨511969313057503216458283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10922012011893401951110037 511969313057503216458283)
        ·
          refine ⟨767953969586254824687425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511969313057503216458283 767953969586254824687425)
          ·
            refine ⟨575965477189691118515569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767953969586254824687425 575965477189691118515569)
            ·
              refine ⟨431974107892268338886677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575965477189691118515569 431974107892268338886677)
              ·
                refine ⟨20248786307450078385313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 431974107892268338886677 20248786307450078385313)
                ·
                  rfl

theorem cell20_133091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_133091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133091 prefixEnd_133091 := by exact prefixLift 133091
  have htrace : WordTrace (prefixWord ++ tailWord_133091) baseStart_133091 baseEnd_133091 := by
    simpa [prefixWord, tailWord_133091, baseEnd_133091] using wordTrace_append hprefix tailTrace_133091
  have hstable : (prefixWord ++ tailWord_133091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133091).length < 2 ^ (prefixWord ++ tailWord_133091).sum := by decide
  have hdescent : baseEnd_133091 < baseStart_133091 := by decide
  rcases family_descends (prefixWord ++ tailWord_133091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133146 : List Nat := [3, 1, 1, 3, 1, 4, 3, 4]
def baseStart_133146 : Nat := 118140960795 + 133146 * 2 ^ 59
def prefixEnd_133146 : Nat := 4983230072969 + 3 ^ 40 * 133146 * 2
def baseEnd_133146 : Nat := 20257154140338162774127

theorem tailTrace_133146 : CollatzResearch.WordTrace tailWord_133146 prefixEnd_133146 20257154140338162774127 := by
  unfold tailWord_133146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214058393910564092880823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3237489050428170914348861 1214058393910564092880823)
  ·
    refine ⟨1821087590865846139321235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1214058393910564092880823 1821087590865846139321235)
    ·
      refine ⟨2731631386298769208981853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1821087590865846139321235 2731631386298769208981853)
      ·
        refine ⟨1024361769862038453368195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2731631386298769208981853 1024361769862038453368195)
        ·
          refine ⟨1536542654793057680052293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024361769862038453368195 1536542654793057680052293)
          ·
            refine ⟨288101747773698315009805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1536542654793057680052293 288101747773698315009805)
            ·
              refine ⟨108038155415136868128677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288101747773698315009805 108038155415136868128677)
              ·
                refine ⟨20257154140338162774127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108038155415136868128677 20257154140338162774127)
                ·
                  rfl

theorem cell20_133146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_133146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133146 prefixEnd_133146 := by exact prefixLift 133146
  have htrace : WordTrace (prefixWord ++ tailWord_133146) baseStart_133146 baseEnd_133146 := by
    simpa [prefixWord, tailWord_133146, baseEnd_133146] using wordTrace_append hprefix tailTrace_133146
  have hstable : (prefixWord ++ tailWord_133146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133146).length < 2 ^ (prefixWord ++ tailWord_133146).sum := by decide
  have hdescent : baseEnd_133146 < baseStart_133146 := by decide
  rcases family_descends (prefixWord ++ tailWord_133146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133170 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 3]
def baseStart_133170 : Nat := 118140960795 + 133170 * 2 ^ 59
def prefixEnd_133170 : Nat := 4983230072969 + 3 ^ 40 * 133170 * 2
def baseEnd_133170 : Nat := 60782416674977071522283

theorem tailTrace_133170 : CollatzResearch.WordTrace tailWord_133170 prefixEnd_133170 60782416674977071522283 := by
  unfold tailWord_133170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214277231888827117599241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3238072618370205646931309 1214277231888827117599241)
  ·
    refine ⟨910707923916620338199431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1214277231888827117599241 910707923916620338199431)
    ·
      refine ⟨1366061885874930507299147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910707923916620338199431 1366061885874930507299147)
      ·
        refine ⟨2049092828812395760948721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1366061885874930507299147 2049092828812395760948721)
        ·
          refine ⟨1536819621609296820711541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2049092828812395760948721 1536819621609296820711541)
          ·
            refine ⟨144076839525871576941707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1536819621609296820711541 144076839525871576941707)
            ·
              refine ⟨216115259288807365412561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144076839525871576941707 216115259288807365412561)
              ·
                refine ⟨162086444466605524059421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216115259288807365412561 162086444466605524059421)
                ·
                  refine ⟨60782416674977071522283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162086444466605524059421 60782416674977071522283)
                  ·
                    rfl

theorem cell20_133170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_133170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133170 prefixEnd_133170 := by exact prefixLift 133170
  have htrace : WordTrace (prefixWord ++ tailWord_133170) baseStart_133170 baseEnd_133170 := by
    simpa [prefixWord, tailWord_133170, baseEnd_133170] using wordTrace_append hprefix tailTrace_133170
  have hstable : (prefixWord ++ tailWord_133170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133170).length < 2 ^ (prefixWord ++ tailWord_133170).sum := by decide
  have hdescent : baseEnd_133170 < baseStart_133170 := by decide
  rcases family_descends (prefixWord ++ tailWord_133170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133177 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 4]
def baseStart_133177 : Nat := 118140960795 + 133177 * 2 ^ 59
def prefixEnd_133177 : Nat := 4983230072969 + 3 ^ 40 * 133177 * 2
def baseEnd_133177 : Nat := 60785611665716158288921

theorem tailTrace_133177 : CollatzResearch.WordTrace tailWord_133177 prefixEnd_133177 60785611665716158288921 := by
  unfold tailWord_133177
  simp only [CollatzResearch.WordTrace]
  refine ⟨4857364238529948665901785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3238242825686632443934523 4857364238529948665901785)
  ·
    refine ⟨3643023178897461499426339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4857364238529948665901785 3643023178897461499426339)
    ·
      refine ⟨5464534768346192249139509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3643023178897461499426339 5464534768346192249139509)
      ·
        refine ⟨512300134532455523356829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5464534768346192249139509 512300134532455523356829)
        ·
          refine ⟨192112550449670821258811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512300134532455523356829 192112550449670821258811)
          ·
            refine ⟨288168825674506231888217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192112550449670821258811 288168825674506231888217)
            ·
              refine ⟨216126619255879673916163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288168825674506231888217 216126619255879673916163)
              ·
                refine ⟨324189928883819510874245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216126619255879673916163 324189928883819510874245)
                ·
                  refine ⟨60785611665716158288921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324189928883819510874245 60785611665716158288921)
                  ·
                    rfl

theorem cell20_133177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_133177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133177 prefixEnd_133177 := by exact prefixLift 133177
  have htrace : WordTrace (prefixWord ++ tailWord_133177) baseStart_133177 baseEnd_133177 := by
    simpa [prefixWord, tailWord_133177, baseEnd_133177] using wordTrace_append hprefix tailTrace_133177
  have hstable : (prefixWord ++ tailWord_133177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133177).length < 2 ^ (prefixWord ++ tailWord_133177).sum := by decide
  have hdescent : baseEnd_133177 < baseStart_133177 := by decide
  rcases family_descends (prefixWord ++ tailWord_133177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133198 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_133198 : Nat := 118140960795 + 133198 * 2 ^ 59
def prefixEnd_133198 : Nat := 4983230072969 + 3 ^ 40 * 133198 * 2
def baseEnd_133198 : Nat := 60795196637933418588835

theorem tailTrace_133198 : CollatzResearch.WordTrace tailWord_133198 prefixEnd_133198 60795196637933418588835 := by
  unfold tailWord_133198
  simp only [CollatzResearch.WordTrace]
  refine ⟨607266271431733656552031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3238753447635912834944165 607266271431733656552031)
  ·
    refine ⟨910899407147600484828047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 607266271431733656552031 910899407147600484828047)
    ·
      refine ⟨1366349110721400727242071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910899407147600484828047 1366349110721400727242071)
      ·
        refine ⟨2049523666082101090863107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1366349110721400727242071 2049523666082101090863107)
        ·
          refine ⟨3074285499123151636294661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049523666082101090863107 3074285499123151636294661)
          ·
            refine ⟨576428531085590931805249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3074285499123151636294661 576428531085590931805249)
            ·
              refine ⟨432321398314193198853937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576428531085590931805249 432321398314193198853937)
              ·
                refine ⟨324241048735644899140453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432321398314193198853937 324241048735644899140453)
                ·
                  refine ⟨60795196637933418588835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324241048735644899140453 60795196637933418588835)
                  ·
                    rfl

theorem cell20_133198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_133198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133198 prefixEnd_133198 := by exact prefixLift 133198
  have htrace : WordTrace (prefixWord ++ tailWord_133198) baseStart_133198 baseEnd_133198 := by
    simpa [prefixWord, tailWord_133198, baseEnd_133198] using wordTrace_append hprefix tailTrace_133198
  have hstable : (prefixWord ++ tailWord_133198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133198).length < 2 ^ (prefixWord ++ tailWord_133198).sum := by decide
  have hdescent : baseEnd_133198 < baseStart_133198 := by decide
  rcases family_descends (prefixWord ++ tailWord_133198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133205 : List Nat := [1, 3, 2, 2, 1, 4, 1, 6]
def baseStart_133205 : Nat := 118140960795 + 133205 * 2 ^ 59
def prefixEnd_133205 : Nat := 4983230072969 + 3 ^ 40 * 133205 * 2
def baseEnd_133205 : Nat := 20266130542890835118491

theorem tailTrace_133205 : CollatzResearch.WordTrace tailWord_133205 prefixEnd_133205 20266130542890835118491 := by
  unfold tailWord_133205
  simp only [CollatzResearch.WordTrace]
  refine ⟨4858385482428509447921069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3238923654952339631947379 4858385482428509447921069)
  ·
    refine ⟨1821894555910691042970401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4858385482428509447921069 1821894555910691042970401)
    ·
      refine ⟨1366420916933018282227801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1821894555910691042970401 1366420916933018282227801)
      ·
        refine ⟨1024815687699763711670851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1366420916933018282227801 1024815687699763711670851)
        ·
          refine ⟨1537223531549645567506277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024815687699763711670851 1537223531549645567506277)
          ·
            refine ⟨288229412165558543907427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1537223531549645567506277 288229412165558543907427)
            ·
              refine ⟨432344118248337815861141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288229412165558543907427 432344118248337815861141)
              ·
                refine ⟨20266130542890835118491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 432344118248337815861141 20266130542890835118491)
                ·
                  rfl

theorem cell20_133205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_133205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133205 prefixEnd_133205 := by exact prefixLift 133205
  have htrace : WordTrace (prefixWord ++ tailWord_133205) baseStart_133205 baseEnd_133205 := by
    simpa [prefixWord, tailWord_133205, baseEnd_133205] using wordTrace_append hprefix tailTrace_133205
  have hstable : (prefixWord ++ tailWord_133205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133205).length < 2 ^ (prefixWord ++ tailWord_133205).sum := by decide
  have hdescent : baseEnd_133205 < baseStart_133205 := by decide
  rcases family_descends (prefixWord ++ tailWord_133205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133219 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_133219 : Nat := 118140960795 + 133219 * 2 ^ 59
def prefixEnd_133219 : Nat := 4983230072969 + 3 ^ 40 * 133219 * 2
def baseEnd_133219 : Nat := 60804781610150678888749

theorem tailTrace_133219 : CollatzResearch.WordTrace tailWord_133219 prefixEnd_133219 60804781610150678888749 := by
  unfold tailWord_133219
  simp only [CollatzResearch.WordTrace]
  refine ⟨4858896104377789838930711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3239264069585193225953807 4858896104377789838930711)
  ·
    refine ⟨7288344156566684758396067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4858896104377789838930711 7288344156566684758396067)
    ·
      refine ⟨10932516234850027137594101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7288344156566684758396067 10932516234850027137594101)
      ·
        refine ⟨1024923397017190044149447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10932516234850027137594101 1024923397017190044149447)
        ·
          refine ⟨1537385095525785066224171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024923397017190044149447 1537385095525785066224171)
          ·
            refine ⟨2306077643288677599336257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1537385095525785066224171 2306077643288677599336257)
            ·
              refine ⟨1729558232466508199502193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2306077643288677599336257 1729558232466508199502193)
              ·
                refine ⟨1297168674349881149626645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729558232466508199502193 1297168674349881149626645)
                ·
                  refine ⟨60804781610150678888749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1297168674349881149626645 60804781610150678888749)
                  ·
                    rfl

theorem cell20_133219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_133219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133219 prefixEnd_133219 := by exact prefixLift 133219
  have htrace : WordTrace (prefixWord ++ tailWord_133219) baseStart_133219 baseEnd_133219 := by
    simpa [prefixWord, tailWord_133219, baseEnd_133219] using wordTrace_append hprefix tailTrace_133219
  have hstable : (prefixWord ++ tailWord_133219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133219).length < 2 ^ (prefixWord ++ tailWord_133219).sum := by decide
  have hdescent : baseEnd_133219 < baseStart_133219 := by decide
  rcases family_descends (prefixWord ++ tailWord_133219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133229 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 3]
def baseStart_133229 : Nat := 118140960795 + 133229 * 2 ^ 59
def prefixEnd_133229 : Nat := 4983230072969 + 3 ^ 40 * 133229 * 2
def baseEnd_133229 : Nat := 60809345882635088555375

theorem tailTrace_133229 : CollatzResearch.WordTrace tailWord_133229 prefixEnd_133229 60809345882635088555375 := by
  unfold tailWord_133229
  simp only [CollatzResearch.WordTrace]
  refine ⟨4859260834341561546794741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3239507222894374364529827 4859260834341561546794741)
  ·
    refine ⟨455555703219521395012007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4859260834341561546794741 455555703219521395012007)
    ·
      refine ⟨683333554829282092518011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455555703219521395012007 683333554829282092518011)
      ·
        refine ⟨1025000332243923138777017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683333554829282092518011 1025000332243923138777017)
        ·
          refine ⟨768750249182942354082763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1025000332243923138777017 768750249182942354082763)
          ·
            refine ⟨1153125373774413531124145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768750249182942354082763 1153125373774413531124145)
            ·
              refine ⟨864844030330810148343109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1153125373774413531124145 864844030330810148343109)
              ·
                refine ⟨162158255687026902814333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 864844030330810148343109 162158255687026902814333)
                ·
                  refine ⟨60809345882635088555375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162158255687026902814333 60809345882635088555375)
                  ·
                    rfl

theorem cell20_133229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_133229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133229 prefixEnd_133229 := by exact prefixLift 133229
  have htrace : WordTrace (prefixWord ++ tailWord_133229) baseStart_133229 baseEnd_133229 := by
    simpa [prefixWord, tailWord_133229, baseEnd_133229] using wordTrace_append hprefix tailTrace_133229
  have hstable : (prefixWord ++ tailWord_133229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133229).length < 2 ^ (prefixWord ++ tailWord_133229).sum := by decide
  have hdescent : baseEnd_133229 < baseStart_133229 := by decide
  rcases family_descends (prefixWord ++ tailWord_133229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133232 : List Nat := [2, 1, 1, 1, 5, 3, 3, 2, 2]
def baseStart_133232 : Nat := 118140960795 + 133232 * 2 ^ 59
def prefixEnd_133232 : Nat := 4983230072969 + 3 ^ 40 * 133232 * 2
def baseEnd_133232 : Nat := 60810715164380411455363

theorem tailTrace_133232 : CollatzResearch.WordTrace tailWord_133232 prefixEnd_133232 60810715164380411455363 := by
  unfold tailWord_133232
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429685126665346529576975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3239580168887128706102633 2429685126665346529576975)
  ·
    refine ⟨3644527689998019794365463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2429685126665346529576975 3644527689998019794365463)
    ·
      refine ⟨5466791534997029691548195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3644527689998019794365463 5466791534997029691548195)
      ·
        refine ⟨8200187302495544537322293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5466791534997029691548195 8200187302495544537322293)
        ·
          refine ⟨768767559608957300373965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8200187302495544537322293 768767559608957300373965)
          ·
            refine ⟨288287834853358987640237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 768767559608957300373965 288287834853358987640237)
            ·
              refine ⟨108107938070009620365089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288287834853358987640237 108107938070009620365089)
              ·
                refine ⟨81080953552507215273817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108107938070009620365089 81080953552507215273817)
                ·
                  refine ⟨60810715164380411455363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81080953552507215273817 60810715164380411455363)
                  ·
                    rfl

theorem cell20_133232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_133232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133232 prefixEnd_133232 := by exact prefixLift 133232
  have htrace : WordTrace (prefixWord ++ tailWord_133232) baseStart_133232 baseEnd_133232 := by
    simpa [prefixWord, tailWord_133232, baseEnd_133232] using wordTrace_append hprefix tailTrace_133232
  have hstable : (prefixWord ++ tailWord_133232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133232).length < 2 ^ (prefixWord ++ tailWord_133232).sum := by decide
  have hdescent : baseEnd_133232 < baseStart_133232 := by decide
  rcases family_descends (prefixWord ++ tailWord_133232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133257 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_133257 : Nat := 118140960795 + 133257 * 2 ^ 59
def prefixEnd_133257 : Nat := 4983230072969 + 3 ^ 40 * 133257 * 2
def baseEnd_133257 : Nat := 60822125845591435621927

theorem tailTrace_133257 : CollatzResearch.WordTrace tailWord_133257 prefixEnd_133257 60822125845591435621927 := by
  unfold tailWord_133257
  simp only [CollatzResearch.WordTrace]
  refine ⟨4860282078240122328814025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3240188052160081552542683 4860282078240122328814025)
  ·
    refine ⟨3645211558680091746610519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4860282078240122328814025 3645211558680091746610519)
    ·
      refine ⟨5467817338020137619915779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645211558680091746610519 5467817338020137619915779)
      ·
        refine ⟨8201726007030206429873669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5467817338020137619915779 8201726007030206429873669)
        ·
          refine ⟨1537823626318163705601313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8201726007030206429873669 1537823626318163705601313)
          ·
            refine ⟨1153367719738622779200985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1537823626318163705601313 1153367719738622779200985)
            ·
              refine ⟨865025789803967084400739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1153367719738622779200985 865025789803967084400739)
              ·
                refine ⟨1297538684705950626601109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865025789803967084400739 1297538684705950626601109)
                ·
                  refine ⟨60822125845591435621927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1297538684705950626601109 60822125845591435621927)
                  ·
                    rfl

theorem cell20_133257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_133257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133257 prefixEnd_133257 := by exact prefixLift 133257
  have htrace : WordTrace (prefixWord ++ tailWord_133257) baseStart_133257 baseEnd_133257 := by
    simpa [prefixWord, tailWord_133257, baseEnd_133257] using wordTrace_append hprefix tailTrace_133257
  have hstable : (prefixWord ++ tailWord_133257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133257).length < 2 ^ (prefixWord ++ tailWord_133257).sum := by decide
  have hdescent : baseEnd_133257 < baseStart_133257 := by decide
  rcases family_descends (prefixWord ++ tailWord_133257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133264 : List Nat := [2, 1, 1, 1, 1, 1, 5, 8]
def baseStart_133264 : Nat := 118140960795 + 133264 * 2 ^ 59
def prefixEnd_133264 : Nat := 4983230072969 + 3 ^ 40 * 133264 * 2
def baseEnd_133264 : Nat := 20275106945443507462855

theorem tailTrace_133264 : CollatzResearch.WordTrace tailWord_133264 prefixEnd_133264 20275106945443507462855 := by
  unfold tailWord_133264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2430268694607381262159423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3240358259476508349545897 2430268694607381262159423)
  ·
    refine ⟨3645403041911071893239135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2430268694607381262159423 3645403041911071893239135)
    ·
      refine ⟨5468104562866607839858703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3645403041911071893239135 5468104562866607839858703)
      ·
        refine ⟨8202156844299911759788055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5468104562866607839858703 8202156844299911759788055)
        ·
          refine ⟨12303235266449867639682083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8202156844299911759788055 12303235266449867639682083)
          ·
            refine ⟨18454852899674801459523125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12303235266449867639682083 18454852899674801459523125)
            ·
              refine ⟨1730142459344512636830293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18454852899674801459523125 1730142459344512636830293)
              ·
                refine ⟨20275106945443507462855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1730142459344512636830293 20275106945443507462855)
                ·
                  rfl

theorem cell20_133264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_133264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133264 prefixEnd_133264 := by exact prefixLift 133264
  have htrace : WordTrace (prefixWord ++ tailWord_133264) baseStart_133264 baseEnd_133264 := by
    simpa [prefixWord, tailWord_133264, baseEnd_133264] using wordTrace_append hprefix tailTrace_133264
  have hstable : (prefixWord ++ tailWord_133264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133264).length < 2 ^ (prefixWord ++ tailWord_133264).sum := by decide
  have hdescent : baseEnd_133264 < baseStart_133264 := by decide
  rcases family_descends (prefixWord ++ tailWord_133264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133284 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_133284 : Nat := 118140960795 + 133284 * 2 ^ 59
def prefixEnd_133284 : Nat := 4983230072969 + 3 ^ 40 * 133284 * 2
def baseEnd_133284 : Nat := 60834449381299341721817

theorem tailTrace_133284 : CollatzResearch.WordTrace tailWord_133284 prefixEnd_133284 60834449381299341721817 := by
  unfold tailWord_133284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2430633424571152970023453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3240844566094870626697937 2430633424571152970023453)
  ·
    refine ⟨911487534214182363758795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2430633424571152970023453 911487534214182363758795)
    ·
      refine ⟨1367231301321273545638193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 911487534214182363758795 1367231301321273545638193)
      ·
        refine ⟨1025423475990955159228645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1367231301321273545638193 1025423475990955159228645)
        ·
          refine ⟨192266901748304092355371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1025423475990955159228645 192266901748304092355371)
          ·
            refine ⟨288400352622456138533057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192266901748304092355371 288400352622456138533057)
            ·
              refine ⟨216300264466842103899793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288400352622456138533057 216300264466842103899793)
              ·
                refine ⟨162225198350131577924845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216300264466842103899793 162225198350131577924845)
                ·
                  refine ⟨60834449381299341721817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162225198350131577924845 60834449381299341721817)
                  ·
                    rfl

theorem cell20_133284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_133284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133284 prefixEnd_133284 := by exact prefixLift 133284
  have htrace : WordTrace (prefixWord ++ tailWord_133284) baseStart_133284 baseEnd_133284 := by
    simpa [prefixWord, tailWord_133284, baseEnd_133284] using wordTrace_append hprefix tailTrace_133284
  have hstable : (prefixWord ++ tailWord_133284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133284).length < 2 ^ (prefixWord ++ tailWord_133284).sum := by decide
  have hdescent : baseEnd_133284 < baseStart_133284 := by decide
  rcases family_descends (prefixWord ++ tailWord_133284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133294 : List Nat := [4, 1, 4, 2, 1, 2, 1, 5]
def baseStart_133294 : Nat := 118140960795 + 133294 * 2 ^ 59
def prefixEnd_133294 : Nat := 4983230072969 + 3 ^ 40 * 133294 * 2
def baseEnd_133294 : Nat := 20279671217927917129481

theorem tailTrace_133294 : CollatzResearch.WordTrace tailWord_133294 prefixEnd_133294 20279671217927917129481 := by
  unfold tailWord_133294
  simp only [CollatzResearch.WordTrace]
  refine ⟨607703947388259705988867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3241087719404051765273957 607703947388259705988867)
  ·
    refine ⟨911555921082389558983301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 607703947388259705988867 911555921082389558983301)
    ·
      refine ⟨170916735202948042309369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 911555921082389558983301 170916735202948042309369)
      ·
        refine ⟨128187551402211031732027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170916735202948042309369 128187551402211031732027)
        ·
          refine ⟨192281327103316547598041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128187551402211031732027 192281327103316547598041)
          ·
            refine ⟨144210995327487410698531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192281327103316547598041 144210995327487410698531)
            ·
              refine ⟨216316492991231116047797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144210995327487410698531 216316492991231116047797)
              ·
                refine ⟨20279671217927917129481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216316492991231116047797 20279671217927917129481)
                ·
                  rfl

theorem cell20_133294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_133294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133294 prefixEnd_133294 := by exact prefixLift 133294
  have htrace : WordTrace (prefixWord ++ tailWord_133294) baseStart_133294 baseEnd_133294 := by
    simpa [prefixWord, tailWord_133294, baseEnd_133294] using wordTrace_append hprefix tailTrace_133294
  have hstable : (prefixWord ++ tailWord_133294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133294).length < 2 ^ (prefixWord ++ tailWord_133294).sum := by decide
  have hdescent : baseEnd_133294 < baseStart_133294 := by decide
  rcases family_descends (prefixWord ++ tailWord_133294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133295 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_133295 : Nat := 118140960795 + 133295 * 2 ^ 59
def prefixEnd_133295 : Nat := 4983230072969 + 3 ^ 40 * 133295 * 2
def baseEnd_133295 : Nat := 60839470081032192355105

theorem tailTrace_133295 : CollatzResearch.WordTrace tailWord_133295 prefixEnd_133295 60839470081032192355105 := by
  unfold tailWord_133295
  simp only [CollatzResearch.WordTrace]
  refine ⟨4861668052102454818697339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3241112034734969879131559 4861668052102454818697339)
  ·
    refine ⟨7292502078153682228046009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4861668052102454818697339 7292502078153682228046009)
    ·
      refine ⟨5469376558615261671034507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7292502078153682228046009 5469376558615261671034507)
      ·
        refine ⟨8204064837922892506551761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5469376558615261671034507 8204064837922892506551761)
        ·
          refine ⟨6153048628442169379913821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8204064837922892506551761 6153048628442169379913821)
          ·
            refine ⟨2307393235665813517467683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6153048628442169379913821 2307393235665813517467683)
            ·
              refine ⟨3461089853498720276201525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2307393235665813517467683 3461089853498720276201525)
              ·
                refine ⟨324477173765505025893893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3461089853498720276201525 324477173765505025893893)
                ·
                  refine ⟨60839470081032192355105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324477173765505025893893 60839470081032192355105)
                  ·
                    rfl

theorem cell20_133295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_133295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133295 prefixEnd_133295 := by exact prefixLift 133295
  have htrace : WordTrace (prefixWord ++ tailWord_133295) baseStart_133295 baseEnd_133295 := by
    simpa [prefixWord, tailWord_133295, baseEnd_133295] using wordTrace_append hprefix tailTrace_133295
  have hstable : (prefixWord ++ tailWord_133295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133295).length < 2 ^ (prefixWord ++ tailWord_133295).sum := by decide
  have hdescent : baseEnd_133295 < baseStart_133295 := by decide
  rcases family_descends (prefixWord ++ tailWord_133295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133312 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_133312 : Nat := 118140960795 + 133312 * 2 ^ 59
def prefixEnd_133312 : Nat := 4983230072969 + 3 ^ 40 * 133312 * 2
def baseEnd_133312 : Nat := 60847229344255688788369

theorem tailTrace_133312 : CollatzResearch.WordTrace tailWord_133312 prefixEnd_133312 60847229344255688788369 := by
  unfold tailWord_133312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431144046520433361033095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3241525395360577814710793 2431144046520433361033095)
  ·
    refine ⟨3646716069780650041549643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2431144046520433361033095 3646716069780650041549643)
    ·
      refine ⟨5470074104670975062324465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3646716069780650041549643 5470074104670975062324465)
      ·
        refine ⟨4102555578503231296743349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5470074104670975062324465 4102555578503231296743349)
        ·
          refine ⟨384614585484677934069689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4102555578503231296743349 384614585484677934069689)
          ·
            refine ⟨288460939113508450552267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384614585484677934069689 288460939113508450552267)
            ·
              refine ⟨432691408670262675828401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288460939113508450552267 432691408670262675828401)
              ·
                refine ⟨324518556502697006871301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432691408670262675828401 324518556502697006871301)
                ·
                  refine ⟨60847229344255688788369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324518556502697006871301 60847229344255688788369)
                  ·
                    rfl

theorem cell20_133312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_133312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133312 prefixEnd_133312 := by exact prefixLift 133312
  have htrace : WordTrace (prefixWord ++ tailWord_133312) baseStart_133312 baseEnd_133312 := by
    simpa [prefixWord, tailWord_133312, baseEnd_133312] using wordTrace_append hprefix tailTrace_133312
  have hstable : (prefixWord ++ tailWord_133312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133312).length < 2 ^ (prefixWord ++ tailWord_133312).sum := by decide
  have hdescent : baseEnd_133312 < baseStart_133312 := by decide
  rcases family_descends (prefixWord ++ tailWord_133312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133384 : List Nat := [2, 1, 3, 2, 3, 3, 1, 3, 2]
def baseStart_133384 : Nat := 118140960795 + 133384 * 2 ^ 59
def prefixEnd_133384 : Nat := 4983230072969 + 3 ^ 40 * 133384 * 2
def baseEnd_133384 : Nat := 60880092106143438388075

theorem tailTrace_133384 : CollatzResearch.WordTrace tailWord_133384 prefixEnd_133384 60880092106143438388075 := by
  unfold tailWord_133384
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432457074390011509343603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3243276099186682012458137 2432457074390011509343603)
  ·
    refine ⟨3648685611585017264015405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2432457074390011509343603 3648685611585017264015405)
    ·
      refine ⟨1368257104344381474005777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3648685611585017264015405 1368257104344381474005777)
      ·
        refine ⟨1026192828258286105504333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1368257104344381474005777 1026192828258286105504333)
        ·
          refine ⟨384822310596857289564125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1026192828258286105504333 384822310596857289564125)
          ·
            refine ⟨144308366473821483586547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384822310596857289564125 144308366473821483586547)
            ·
              refine ⟨216462549710732225379821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144308366473821483586547 216462549710732225379821)
              ·
                refine ⟨81173456141524584517433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216462549710732225379821 81173456141524584517433)
                ·
                  refine ⟨60880092106143438388075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81173456141524584517433 60880092106143438388075)
                  ·
                    rfl

theorem cell20_133384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_133384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133384 prefixEnd_133384 := by exact prefixLift 133384
  have htrace : WordTrace (prefixWord ++ tailWord_133384) baseStart_133384 baseEnd_133384 := by
    simpa [prefixWord, tailWord_133384, baseEnd_133384] using wordTrace_append hprefix tailTrace_133384
  have hstable : (prefixWord ++ tailWord_133384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133384).length < 2 ^ (prefixWord ++ tailWord_133384).sum := by decide
  have hdescent : baseEnd_133384 < baseStart_133384 := by decide
  rcases family_descends (prefixWord ++ tailWord_133384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133433 : List Nat := [1, 2, 1, 6, 1, 1, 2, 6]
def baseStart_133433 : Nat := 118140960795 + 133433 * 2 ^ 59
def prefixEnd_133433 : Nat := 4983230072969 + 3 ^ 40 * 133433 * 2
def baseEnd_133433 : Nat := 20300819013772348584847

theorem tailTrace_133433 : CollatzResearch.WordTrace tailWord_133433 prefixEnd_133433 20300819013772348584847 := by
  unfold tailWord_133433
  simp only [CollatzResearch.WordTrace]
  refine ⟨4866701325602504387220953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3244467550401669591480635 4866701325602504387220953)
  ·
    refine ⟨3650025994201878290415715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4866701325602504387220953 3650025994201878290415715)
    ·
      refine ⟨5475038991302817435623573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3650025994201878290415715 5475038991302817435623573)
      ·
        refine ⟨256642452717319567294855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5475038991302817435623573 256642452717319567294855)
        ·
          refine ⟨384963679075979350942283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256642452717319567294855 384963679075979350942283)
          ·
            refine ⟨577445518613969026413425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384963679075979350942283 577445518613969026413425)
            ·
              refine ⟨433084138960476769810069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577445518613969026413425 433084138960476769810069)
              ·
                refine ⟨20300819013772348584847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 433084138960476769810069 20300819013772348584847)
                ·
                  rfl

theorem cell20_133433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_133433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133433 prefixEnd_133433 := by exact prefixLift 133433
  have htrace : WordTrace (prefixWord ++ tailWord_133433) baseStart_133433 baseEnd_133433 := by
    simpa [prefixWord, tailWord_133433, baseEnd_133433] using wordTrace_append hprefix tailTrace_133433
  have hstable : (prefixWord ++ tailWord_133433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133433).length < 2 ^ (prefixWord ++ tailWord_133433).sum := by decide
  have hdescent : baseEnd_133433 < baseStart_133433 := by decide
  rcases family_descends (prefixWord ++ tailWord_133433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133457 : List Nat := [1, 2, 2, 1, 4, 3, 2, 2, 3]
def baseStart_133457 : Nat := 118140960795 + 133457 * 2 ^ 59
def prefixEnd_133457 : Nat := 4983230072969 + 3 ^ 40 * 133457 * 2
def baseEnd_133457 : Nat := 60913411295279628954443

theorem tailTrace_133457 : CollatzResearch.WordTrace tailWord_133457 prefixEnd_133457 60913411295279628954443 := by
  unfold tailWord_133457
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867576677515556486094625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3245051118343704324063083 4867576677515556486094625)
  ·
    refine ⟨3650682508136667364570969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4867576677515556486094625 3650682508136667364570969)
    ·
      refine ⟨2738011881102500523428227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3650682508136667364570969 2738011881102500523428227)
      ·
        refine ⟨4107017821653750785142341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2738011881102500523428227 4107017821653750785142341)
        ·
          refine ⟨770065841560078272214189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4107017821653750785142341 770065841560078272214189)
          ·
            refine ⟨288774690585029352080321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 770065841560078272214189 288774690585029352080321)
            ·
              refine ⟨216581017938772014060241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288774690585029352080321 216581017938772014060241)
              ·
                refine ⟨162435763454079010545181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216581017938772014060241 162435763454079010545181)
                ·
                  refine ⟨60913411295279628954443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162435763454079010545181 60913411295279628954443)
                  ·
                    rfl

theorem cell20_133457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_133457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133457 prefixEnd_133457 := by exact prefixLift 133457
  have htrace : WordTrace (prefixWord ++ tailWord_133457) baseStart_133457 baseEnd_133457 := by
    simpa [prefixWord, tailWord_133457, baseEnd_133457] using wordTrace_append hprefix tailTrace_133457
  have hstable : (prefixWord ++ tailWord_133457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133457).length < 2 ^ (prefixWord ++ tailWord_133457).sum := by decide
  have hdescent : baseEnd_133457 < baseStart_133457 := by decide
  rcases family_descends (prefixWord ++ tailWord_133457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133460 : List Nat := [2, 4, 1, 1, 2, 2, 4, 2, 2]
def baseStart_133460 : Nat := 118140960795 + 133460 * 2 ^ 59
def prefixEnd_133460 : Nat := 4983230072969 + 3 ^ 40 * 133460 * 2
def baseEnd_133460 : Nat := 60914780577024951854431

theorem tailTrace_133460 : CollatzResearch.WordTrace tailWord_133460 prefixEnd_133460 60914780577024951854431 := by
  unfold tailWord_133460
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433843048252343999226917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3245124064336458665635889 2433843048252343999226917)
  ·
    refine ⟨456345571547314499855047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2433843048252343999226917 456345571547314499855047)
    ·
      refine ⟨684518357320971749782571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456345571547314499855047 684518357320971749782571)
      ·
        refine ⟨1026777535981457624673857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684518357320971749782571 1026777535981457624673857)
        ·
          refine ⟨770083151986093218505393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1026777535981457624673857 770083151986093218505393)
          ·
            refine ⟨577562363989569913879045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770083151986093218505393 577562363989569913879045)
            ·
              refine ⟨108292943248044358852321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 577562363989569913879045 108292943248044358852321)
              ·
                refine ⟨81219707436033269139241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108292943248044358852321 81219707436033269139241)
                ·
                  refine ⟨60914780577024951854431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81219707436033269139241 60914780577024951854431)
                  ·
                    rfl

theorem cell20_133460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_133460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133460 prefixEnd_133460 := by exact prefixLift 133460
  have htrace : WordTrace (prefixWord ++ tailWord_133460) baseStart_133460 baseEnd_133460 := by
    simpa [prefixWord, tailWord_133460, baseEnd_133460] using wordTrace_append hprefix tailTrace_133460
  have hstable : (prefixWord ++ tailWord_133460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133460).length < 2 ^ (prefixWord ++ tailWord_133460).sum := by decide
  have hdescent : baseEnd_133460 < baseStart_133460 := by decide
  rcases family_descends (prefixWord ++ tailWord_133460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133516 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_133516 : Nat := 118140960795 + 133516 * 2 ^ 59
def prefixEnd_133516 : Nat := 4983230072969 + 3 ^ 40 * 133516 * 2
def baseEnd_133516 : Nat := 60940340502937645987535

theorem tailTrace_133516 : CollatzResearch.WordTrace tailWord_133516 prefixEnd_133516 60940340502937645987535 := by
  unfold tailWord_133516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2434864292150904781246201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3246485722867873041661601 2434864292150904781246201)
  ·
    refine ⟨1826148219113178585934651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2434864292150904781246201 1826148219113178585934651)
    ·
      refine ⟨2739222328669767878901977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1826148219113178585934651 2739222328669767878901977)
      ·
        refine ⟨2054416746502325909176483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2739222328669767878901977 2054416746502325909176483)
        ·
          refine ⟨3081625119753488863764725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2054416746502325909176483 3081625119753488863764725)
          ·
            refine ⟨288902354976889580977943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3081625119753488863764725 288902354976889580977943)
            ·
              refine ⟨433353532465334371466915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288902354976889580977943 433353532465334371466915)
              ·
                refine ⟨650030298698001557200373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433353532465334371466915 650030298698001557200373)
                ·
                  refine ⟨60940340502937645987535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 650030298698001557200373 60940340502937645987535)
                  ·
                    rfl

theorem cell20_133516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_133516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133516 prefixEnd_133516 := by exact prefixLift 133516
  have htrace : WordTrace (prefixWord ++ tailWord_133516) baseStart_133516 baseEnd_133516 := by
    simpa [prefixWord, tailWord_133516, baseEnd_133516] using wordTrace_append hprefix tailTrace_133516
  have hstable : (prefixWord ++ tailWord_133516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133516).length < 2 ^ (prefixWord ++ tailWord_133516).sum := by decide
  have hdescent : baseEnd_133516 < baseStart_133516 := by decide
  rcases family_descends (prefixWord ++ tailWord_133516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133588 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 3]
def baseStart_133588 : Nat := 118140960795 + 133588 * 2 ^ 59
def prefixEnd_133588 : Nat := 4983230072969 + 3 ^ 40 * 133588 * 2
def baseEnd_133588 : Nat := 60973203264825395587241

theorem tailTrace_133588 : CollatzResearch.WordTrace tailWord_133588 prefixEnd_133588 60973203264825395587241 := by
  unfold tailWord_133588
  simp only [CollatzResearch.WordTrace]
  refine ⟨2436177320020482929556709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3248236426693977239408945 2436177320020482929556709)
  ·
    refine ⟨456783247503840549291883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2436177320020482929556709 456783247503840549291883)
    ·
      refine ⟨685174871255760823937825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456783247503840549291883 685174871255760823937825)
      ·
        refine ⟨513881153441820617953369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685174871255760823937825 513881153441820617953369)
        ·
          refine ⟨385410865081365463465027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513881153441820617953369 385410865081365463465027)
          ·
            refine ⟨578116297622048195197541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385410865081365463465027 578116297622048195197541)
            ·
              refine ⟨108396805804134036599539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 578116297622048195197541 108396805804134036599539)
              ·
                refine ⟨162595208706201054899309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108396805804134036599539 162595208706201054899309)
                ·
                  refine ⟨60973203264825395587241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162595208706201054899309 60973203264825395587241)
                  ·
                    rfl

theorem cell20_133588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_133588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133588 prefixEnd_133588 := by exact prefixLift 133588
  have htrace : WordTrace (prefixWord ++ tailWord_133588) baseStart_133588 baseEnd_133588 := by
    simpa [prefixWord, tailWord_133588, baseEnd_133588] using wordTrace_append hprefix tailTrace_133588
  have hstable : (prefixWord ++ tailWord_133588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133588).length < 2 ^ (prefixWord ++ tailWord_133588).sum := by decide
  have hdescent : baseEnd_133588 < baseStart_133588 := by decide
  rcases family_descends (prefixWord ++ tailWord_133588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133616 : List Nat := [2, 1, 1, 1, 3, 3, 2, 5, 2]
def baseStart_133616 : Nat := 118140960795 + 133616 * 2 ^ 59
def prefixEnd_133616 : Nat := 4983230072969 + 3 ^ 40 * 133616 * 2
def baseEnd_133616 : Nat := 60985983227781742653793

theorem tailTrace_133616 : CollatzResearch.WordTrace tailWord_133616 prefixEnd_133616 60985983227781742653793 := by
  unfold tailWord_133616
  simp only [CollatzResearch.WordTrace]
  refine ⟨2436687941969763320566351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3248917255959684427421801 2436687941969763320566351)
  ·
    refine ⟨3655031912954644980849527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2436687941969763320566351 3655031912954644980849527)
    ·
      refine ⟨5482547869431967471274291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3655031912954644980849527 5482547869431967471274291)
      ·
        refine ⟨8223821804147951206911437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5482547869431967471274291 8223821804147951206911437)
        ·
          refine ⟨3083933176555481702591789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8223821804147951206911437 3083933176555481702591789)
          ·
            refine ⟨1156474941208305638471921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3083933176555481702591789 1156474941208305638471921)
            ·
              refine ⟨867356205906229228853941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156474941208305638471921 867356205906229228853941)
              ·
                refine ⟨81314644303708990205057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 867356205906229228853941 81314644303708990205057)
                ·
                  refine ⟨60985983227781742653793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81314644303708990205057 60985983227781742653793)
                  ·
                    rfl

theorem cell20_133616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_133616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133616 prefixEnd_133616 := by exact prefixLift 133616
  have htrace : WordTrace (prefixWord ++ tailWord_133616) baseStart_133616 baseEnd_133616 := by
    simpa [prefixWord, tailWord_133616, baseEnd_133616] using wordTrace_append hprefix tailTrace_133616
  have hstable : (prefixWord ++ tailWord_133616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133616).length < 2 ^ (prefixWord ++ tailWord_133616).sum := by decide
  have hdescent : baseEnd_133616 < baseStart_133616 := by decide
  rcases family_descends (prefixWord ++ tailWord_133616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133633 : List Nat := [1, 2, 4, 1, 3, 2, 1, 4, 2]
def baseStart_133633 : Nat := 118140960795 + 133633 * 2 ^ 59
def prefixEnd_133633 : Nat := 4983230072969 + 3 ^ 40 * 133633 * 2
def baseEnd_133633 : Nat := 60993742491005239087057

theorem tailTrace_133633 : CollatzResearch.WordTrace tailWord_133633 prefixEnd_133633 60993742491005239087057 := by
  unfold tailWord_133633
  simp only [CollatzResearch.WordTrace]
  refine ⟨4873995924877938544501553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3249330616585292363001035 4873995924877938544501553)
  ·
    refine ⟨3655496943658453908376165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4873995924877938544501553 3655496943658453908376165)
    ·
      refine ⟨685405676935960107820531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3655496943658453908376165 685405676935960107820531)
      ·
        refine ⟨1028108515403940161730797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685405676935960107820531 1028108515403940161730797)
        ·
          refine ⟨385540693276477560649049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1028108515403940161730797 385540693276477560649049)
          ·
            refine ⟨289155519957358170486787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385540693276477560649049 289155519957358170486787)
            ·
              refine ⟨433733279936037255730181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289155519957358170486787 433733279936037255730181)
              ·
                refine ⟨81324989988006985449409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433733279936037255730181 81324989988006985449409)
                ·
                  refine ⟨60993742491005239087057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81324989988006985449409 60993742491005239087057)
                  ·
                    rfl

theorem cell20_133633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_133633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133633 prefixEnd_133633 := by exact prefixLift 133633
  have htrace : WordTrace (prefixWord ++ tailWord_133633) baseStart_133633 baseEnd_133633 := by
    simpa [prefixWord, tailWord_133633, baseEnd_133633] using wordTrace_append hprefix tailTrace_133633
  have hstable : (prefixWord ++ tailWord_133633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133633).length < 2 ^ (prefixWord ++ tailWord_133633).sum := by decide
  have hdescent : baseEnd_133633 < baseStart_133633 := by decide
  rcases family_descends (prefixWord ++ tailWord_133633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133677 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 3]
def baseStart_133677 : Nat := 118140960795 + 133677 * 2 ^ 59
def prefixEnd_133677 : Nat := 4983230072969 + 3 ^ 40 * 133677 * 2
def baseEnd_133677 : Nat := 61013825289936641620211

theorem tailTrace_133677 : CollatzResearch.WordTrace tailWord_133677 prefixEnd_133677 61013825289936641620211 := by
  unfold tailWord_133677
  simp only [CollatzResearch.WordTrace]
  refine ⟨4875600736718534059103285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3250400491145689372735523 4875600736718534059103285)
  ·
    refine ⟨457087569067362568040933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4875600736718534059103285 457087569067362568040933)
    ·
      refine ⟨85703919200130481507675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 457087569067362568040933 85703919200130481507675)
      ·
        refine ⟨128555878800195722261513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85703919200130481507675 128555878800195722261513)
        ·
          refine ⟨96416909100146791696135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128555878800195722261513 96416909100146791696135)
          ·
            refine ⟨144625363650220187544203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96416909100146791696135 144625363650220187544203)
            ·
              refine ⟨216938045475330281316305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144625363650220187544203 216938045475330281316305)
              ·
                refine ⟨162703534106497710987229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216938045475330281316305 162703534106497710987229)
                ·
                  refine ⟨61013825289936641620211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162703534106497710987229 61013825289936641620211)
                  ·
                    rfl

theorem cell20_133677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_133677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133677 prefixEnd_133677 := by exact prefixLift 133677
  have htrace : WordTrace (prefixWord ++ tailWord_133677) baseStart_133677 baseEnd_133677 := by
    simpa [prefixWord, tailWord_133677, baseEnd_133677] using wordTrace_append hprefix tailTrace_133677
  have hstable : (prefixWord ++ tailWord_133677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133677).length < 2 ^ (prefixWord ++ tailWord_133677).sum := by decide
  have hdescent : baseEnd_133677 < baseStart_133677 := by decide
  rcases family_descends (prefixWord ++ tailWord_133677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133692 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 4]
def baseStart_133692 : Nat := 118140960795 + 133692 * 2 ^ 59
def prefixEnd_133692 : Nat := 4983230072969 + 3 ^ 40 * 133692 * 2
def baseEnd_133692 : Nat := 61020671698663256120149

theorem tailTrace_133692 : CollatzResearch.WordTrace tailWord_133692 prefixEnd_133692 61020671698663256120149 := by
  unfold tailWord_133692
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438073915832095810449665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3250765221109461080599553 2438073915832095810449665)
  ·
    refine ⟨1828555436874071857837249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2438073915832095810449665 1828555436874071857837249)
    ·
      refine ⟨1371416577655553893377937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1828555436874071857837249 1371416577655553893377937)
      ·
        refine ⟨1028562433241665420033453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371416577655553893377937 1028562433241665420033453)
        ·
          refine ⟨385710912465624532512545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1028562433241665420033453 385710912465624532512545)
          ·
            refine ⟨289283184349218399384409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385710912465624532512545 289283184349218399384409)
            ·
              refine ⟨216962388261913799538307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289283184349218399384409 216962388261913799538307)
              ·
                refine ⟨325443582392870699307461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216962388261913799538307 325443582392870699307461)
                ·
                  refine ⟨61020671698663256120149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325443582392870699307461 61020671698663256120149)
                  ·
                    rfl

theorem cell20_133692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_133692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133692 prefixEnd_133692 := by exact prefixLift 133692
  have htrace : WordTrace (prefixWord ++ tailWord_133692) baseStart_133692 baseEnd_133692 := by
    simpa [prefixWord, tailWord_133692, baseEnd_133692] using wordTrace_append hprefix tailTrace_133692
  have hstable : (prefixWord ++ tailWord_133692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133692).length < 2 ^ (prefixWord ++ tailWord_133692).sum := by decide
  have hdescent : baseEnd_133692 < baseStart_133692 := by decide
  rcases family_descends (prefixWord ++ tailWord_133692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133713 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_133713 : Nat := 118140960795 + 133713 * 2 ^ 59
def prefixEnd_133713 : Nat := 4983230072969 + 3 ^ 40 * 133713 * 2
def baseEnd_133713 : Nat := 61030256670880516420063

theorem tailTrace_133713 : CollatzResearch.WordTrace tailWord_133713 prefixEnd_133713 61030256670880516420063 := by
  unfold tailWord_133713
  simp only [CollatzResearch.WordTrace]
  refine ⟨4876913764588112207413793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3251275843058741471609195 4876913764588112207413793)
  ·
    refine ⟨3657685323441084155560345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4876913764588112207413793 3657685323441084155560345)
    ·
      refine ⟨2743263992580813116670259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3657685323441084155560345 2743263992580813116670259)
      ·
        refine ⟨4114895988871219675005389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2743263992580813116670259 4114895988871219675005389)
        ·
          refine ⟨1543085995826707378127021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4114895988871219675005389 1543085995826707378127021)
          ·
            refine ⟨578657248435015266797633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1543085995826707378127021 578657248435015266797633)
            ·
              refine ⟨433992936326261450098225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578657248435015266797633 433992936326261450098225)
              ·
                refine ⟨325494702244696087573669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433992936326261450098225 325494702244696087573669)
                ·
                  refine ⟨61030256670880516420063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325494702244696087573669 61030256670880516420063)
                  ·
                    rfl

theorem cell20_133713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_133713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133713 prefixEnd_133713 := by exact prefixLift 133713
  have htrace : WordTrace (prefixWord ++ tailWord_133713) baseStart_133713 baseEnd_133713 := by
    simpa [prefixWord, tailWord_133713, baseEnd_133713] using wordTrace_append hprefix tailTrace_133713
  have hstable : (prefixWord ++ tailWord_133713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133713).length < 2 ^ (prefixWord ++ tailWord_133713).sum := by decide
  have hdescent : baseEnd_133713 < baseStart_133713 := by decide
  rcases family_descends (prefixWord ++ tailWord_133713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133716 : List Nat := [2, 4, 1, 1, 1, 5, 2, 4]
def baseStart_133716 : Nat := 118140960795 + 133716 * 2 ^ 59
def prefixEnd_133716 : Nat := 4983230072969 + 3 ^ 40 * 133716 * 2
def baseEnd_133716 : Nat := 20343875317541946440017

theorem tailTrace_133716 : CollatzResearch.WordTrace tailWord_133716 prefixEnd_133716 20343875317541946440017 := by
  unfold tailWord_133716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438511591788621859886501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3251348789051495813182001 2438511591788621859886501)
  ·
    refine ⟨457220923460366598728719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2438511591788621859886501 457220923460366598728719)
    ·
      refine ⟨685831385190549898093079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457220923460366598728719 685831385190549898093079)
      ·
        refine ⟨1028747077785824847139619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685831385190549898093079 1028747077785824847139619)
        ·
          refine ⟨1543120616678737270709429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028747077785824847139619 1543120616678737270709429)
          ·
            refine ⟨144667557813631619129009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1543120616678737270709429 144667557813631619129009)
            ·
              refine ⟨108500668360223714346757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144667557813631619129009 108500668360223714346757)
              ·
                refine ⟨20343875317541946440017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108500668360223714346757 20343875317541946440017)
                ·
                  rfl

theorem cell20_133716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_133716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133716 prefixEnd_133716 := by exact prefixLift 133716
  have htrace : WordTrace (prefixWord ++ tailWord_133716) baseStart_133716 baseEnd_133716 := by
    simpa [prefixWord, tailWord_133716, baseEnd_133716] using wordTrace_append hprefix tailTrace_133716
  have hstable : (prefixWord ++ tailWord_133716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133716).length < 2 ^ (prefixWord ++ tailWord_133716).sum := by decide
  have hdescent : baseEnd_133716 < baseStart_133716 := by decide
  rcases family_descends (prefixWord ++ tailWord_133716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133751 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_133751 : Nat := 118140960795 + 133751 * 2 ^ 59
def prefixEnd_133751 : Nat := 4983230072969 + 3 ^ 40 * 133751 * 2
def baseEnd_133751 : Nat := 61047600906321273153241

theorem tailTrace_133751 : CollatzResearch.WordTrace tailWord_133751 prefixEnd_133751 61047600906321273153241 := by
  unfold tailWord_133751
  simp only [CollatzResearch.WordTrace]
  refine ⟨4878299738450444697297107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3252199825633629798198071 4878299738450444697297107)
  ·
    refine ⟨7317449607675667045945661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4878299738450444697297107 7317449607675667045945661)
    ·
      refine ⟨2744043602878375142229623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7317449607675667045945661 2744043602878375142229623)
      ·
        refine ⟨4116065404317562713344435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744043602878375142229623 4116065404317562713344435)
        ·
          refine ⟨6174098106476344070016653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4116065404317562713344435 6174098106476344070016653)
          ·
            refine ⟨2315286789928629026256245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6174098106476344070016653 2315286789928629026256245)
            ·
              refine ⟨217058136555808971211523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2315286789928629026256245 217058136555808971211523)
              ·
                refine ⟨325587204833713456817285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217058136555808971211523 325587204833713456817285)
                ·
                  refine ⟨61047600906321273153241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325587204833713456817285 61047600906321273153241)
                  ·
                    rfl

theorem cell20_133751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_133751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133751 prefixEnd_133751 := by exact prefixLift 133751
  have htrace : WordTrace (prefixWord ++ tailWord_133751) baseStart_133751 baseEnd_133751 := by
    simpa [prefixWord, tailWord_133751, baseEnd_133751] using wordTrace_append hprefix tailTrace_133751
  have hstable : (prefixWord ++ tailWord_133751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133751).length < 2 ^ (prefixWord ++ tailWord_133751).sum := by decide
  have hdescent : baseEnd_133751 < baseStart_133751 := by decide
  rcases family_descends (prefixWord ++ tailWord_133751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133757 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 3]
def baseStart_133757 : Nat := 118140960795 + 133757 * 2 ^ 59
def prefixEnd_133757 : Nat := 4983230072969 + 3 ^ 40 * 133757 * 2
def baseEnd_133757 : Nat := 61050339469811918953217

theorem tailTrace_133757 : CollatzResearch.WordTrace tailWord_133757 prefixEnd_133757 61050339469811918953217 := by
  unfold tailWord_133757
  simp only [CollatzResearch.WordTrace]
  refine ⟨4878518576428707722015525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3252345717619138481343683 4878518576428707722015525)
  ·
    refine ⟨914722233080382697877911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4878518576428707722015525 914722233080382697877911)
    ·
      refine ⟨1372083349620574046816867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914722233080382697877911 1372083349620574046816867)
      ·
        refine ⟨2058125024430861070225301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372083349620574046816867 2058125024430861070225301)
        ·
          refine ⟨96474610520196612666811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2058125024430861070225301 96474610520196612666811)
          ·
            refine ⟨144711915780294919000217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96474610520196612666811 144711915780294919000217)
            ·
              refine ⟨108533936835221189250163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144711915780294919000217 108533936835221189250163)
              ·
                refine ⟨162800905252831783875245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108533936835221189250163 162800905252831783875245)
                ·
                  refine ⟨61050339469811918953217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162800905252831783875245 61050339469811918953217)
                  ·
                    rfl

theorem cell20_133757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_133757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133757 prefixEnd_133757 := by exact prefixLift 133757
  have htrace : WordTrace (prefixWord ++ tailWord_133757) baseStart_133757 baseEnd_133757 := by
    simpa [prefixWord, tailWord_133757, baseEnd_133757] using wordTrace_append hprefix tailTrace_133757
  have hstable : (prefixWord ++ tailWord_133757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133757).length < 2 ^ (prefixWord ++ tailWord_133757).sum := by decide
  have hdescent : baseEnd_133757 < baseStart_133757 := by decide
  rcases family_descends (prefixWord ++ tailWord_133757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133809 : List Nat := [1, 2, 2, 6, 2, 1, 1, 5]
def baseStart_133809 : Nat := 118140960795 + 133809 * 2 ^ 59
def prefixEnd_133809 : Nat := 4983230072969 + 3 ^ 40 * 133809 * 2
def baseEnd_133809 : Nat := 20358024562243616406557

theorem tailTrace_133809 : CollatzResearch.WordTrace tailWord_133809 prefixEnd_133809 20358024562243616406557 := by
  unfold tailWord_133809
  simp only [CollatzResearch.WordTrace]
  refine ⟨4880415172240320602908481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3253610114826880401938987 4880415172240320602908481)
  ·
    refine ⟨3660311379180240452181361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4880415172240320602908481 3660311379180240452181361)
    ·
      refine ⟨2745233534385180339136021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3660311379180240452181361 2745233534385180339136021)
      ·
        refine ⟨128682821924305328397001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2745233534385180339136021 128682821924305328397001)
        ·
          refine ⟨96512116443228996297751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128682821924305328397001 96512116443228996297751)
          ·
            refine ⟨144768174664843494446627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96512116443228996297751 144768174664843494446627)
            ·
              refine ⟨217152261997265241669941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144768174664843494446627 217152261997265241669941)
              ·
                refine ⟨20358024562243616406557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217152261997265241669941 20358024562243616406557)
                ·
                  rfl

theorem cell20_133809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 5].length) (baseStart_133809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133809 prefixEnd_133809 := by exact prefixLift 133809
  have htrace : WordTrace (prefixWord ++ tailWord_133809) baseStart_133809 baseEnd_133809 := by
    simpa [prefixWord, tailWord_133809, baseEnd_133809] using wordTrace_append hprefix tailTrace_133809
  have hstable : (prefixWord ++ tailWord_133809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133809).length < 2 ^ (prefixWord ++ tailWord_133809).sum := by decide
  have hdescent : baseEnd_133809 < baseStart_133809 := by decide
  rcases family_descends (prefixWord ++ tailWord_133809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133813 : List Nat := [1, 3, 3, 3, 1, 1, 3, 5]
def baseStart_133813 : Nat := 118140960795 + 133813 * 2 ^ 59
def prefixEnd_133813 : Nat := 4983230072969 + 3 ^ 40 * 133813 * 2
def baseEnd_133813 : Nat := 20358633131908204362107

theorem tailTrace_133813 : CollatzResearch.WordTrace tailWord_133813 prefixEnd_133813 20358633131908204362107 := by
  unfold tailWord_133813
  simp only [CollatzResearch.WordTrace]
  refine ⟨4880561064225829286054093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3253707376150552857369395 4880561064225829286054093)
  ·
    refine ⟨1830210399084685982270285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4880561064225829286054093 1830210399084685982270285)
    ·
      refine ⟨686328899656757243351357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1830210399084685982270285 686328899656757243351357)
      ·
        refine ⟨257373337371283966256759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 686328899656757243351357 257373337371283966256759)
        ·
          refine ⟨386060006056925949385139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257373337371283966256759 386060006056925949385139)
          ·
            refine ⟨579090009085388924077709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386060006056925949385139 579090009085388924077709)
            ·
              refine ⟨217158753407020846529141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 579090009085388924077709 217158753407020846529141)
              ·
                refine ⟨20358633131908204362107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217158753407020846529141 20358633131908204362107)
                ·
                  rfl

theorem cell20_133813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_133813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133813 prefixEnd_133813 := by exact prefixLift 133813
  have htrace : WordTrace (prefixWord ++ tailWord_133813) baseStart_133813 baseEnd_133813 := by
    simpa [prefixWord, tailWord_133813, baseEnd_133813] using wordTrace_append hprefix tailTrace_133813
  have hstable : (prefixWord ++ tailWord_133813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133813).length < 2 ^ (prefixWord ++ tailWord_133813).sum := by decide
  have hdescent : baseEnd_133813 < baseStart_133813 := by decide
  rcases family_descends (prefixWord ++ tailWord_133813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133820 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_133820 : Nat := 118140960795 + 133820 * 2 ^ 59
def prefixEnd_133820 : Nat := 4983230072969 + 3 ^ 40 * 133820 * 2
def baseEnd_133820 : Nat := 61079094386463699852959

theorem tailTrace_133820 : CollatzResearch.WordTrace tailWord_133820 prefixEnd_133820 61079094386463699852959 := by
  unfold tailWord_133820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2440408187600234740779457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3253877583466979654372609 2440408187600234740779457)
  ·
    refine ⟨1830306140700176055584593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2440408187600234740779457 1830306140700176055584593)
    ·
      refine ⟨1372729605525132041688445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1830306140700176055584593 1372729605525132041688445)
      ·
        refine ⟨514773602071924515633167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1372729605525132041688445 514773602071924515633167)
        ·
          refine ⟨772160403107886773449751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514773602071924515633167 772160403107886773449751)
          ·
            refine ⟨1158240604661830160174627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772160403107886773449751 1158240604661830160174627)
            ·
              refine ⟨1737360906992745240261941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158240604661830160174627 1737360906992745240261941)
              ·
                refine ⟨162877585030569866274557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1737360906992745240261941 162877585030569866274557)
                ·
                  refine ⟨61079094386463699852959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162877585030569866274557 61079094386463699852959)
                  ·
                    rfl

theorem cell20_133820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_133820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133820 prefixEnd_133820 := by exact prefixLift 133820
  have htrace : WordTrace (prefixWord ++ tailWord_133820) baseStart_133820 baseEnd_133820 := by
    simpa [prefixWord, tailWord_133820, baseEnd_133820] using wordTrace_append hprefix tailTrace_133820
  have hstable : (prefixWord ++ tailWord_133820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133820).length < 2 ^ (prefixWord ++ tailWord_133820).sum := by decide
  have hdescent : baseEnd_133820 < baseStart_133820 := by decide
  rcases family_descends (prefixWord ++ tailWord_133820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133841 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_133841 : Nat := 118140960795 + 133841 * 2 ^ 59
def prefixEnd_133841 : Nat := 4983230072969 + 3 ^ 40 * 133841 * 2
def baseEnd_133841 : Nat := 61088679358680960152873

theorem tailTrace_133841 : CollatzResearch.WordTrace tailWord_133841 prefixEnd_133841 61088679358680960152873 := by
  unfold tailWord_133841
  simp only [CollatzResearch.WordTrace]
  refine ⟨4881582308124390068073377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3254388205416260045382251 4881582308124390068073377)
  ·
    refine ⟨3661186731093292551055033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4881582308124390068073377 3661186731093292551055033)
    ·
      refine ⟨2745890048319969413291275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3661186731093292551055033 2745890048319969413291275)
      ·
        refine ⟨4118835072479954119936913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2745890048319969413291275 4118835072479954119936913)
        ·
          refine ⟨3089126304359965589952685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4118835072479954119936913 3089126304359965589952685)
          ·
            refine ⟨1158422364134987096232257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3089126304359965589952685 1158422364134987096232257)
            ·
              refine ⟨868816773101240322174193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158422364134987096232257 868816773101240322174193)
              ·
                refine ⟨651612579825930241630645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868816773101240322174193 651612579825930241630645)
                ·
                  refine ⟨61088679358680960152873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 651612579825930241630645 61088679358680960152873)
                  ·
                    rfl

theorem cell20_133841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_133841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133841 prefixEnd_133841 := by exact prefixLift 133841
  have htrace : WordTrace (prefixWord ++ tailWord_133841) baseStart_133841 baseEnd_133841 := by
    simpa [prefixWord, tailWord_133841, baseEnd_133841] using wordTrace_append hprefix tailTrace_133841
  have hstable : (prefixWord ++ tailWord_133841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133841).length < 2 ^ (prefixWord ++ tailWord_133841).sum := by decide
  have hdescent : baseEnd_133841 < baseStart_133841 := by decide
  rcases family_descends (prefixWord ++ tailWord_133841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133906 : List Nat := [3, 2, 4, 1, 2, 2, 6]
def baseStart_133906 : Nat := 118140960795 + 133906 * 2 ^ 59
def prefixEnd_133906 : Nat := 4983230072969 + 3 ^ 40 * 133906 * 2
def baseEnd_133906 : Nat := 6790927458869958109549

theorem tailTrace_133906 : CollatzResearch.WordTrace tailWord_133906 prefixEnd_133906 6790927458869958109549 := by
  unfold tailWord_133906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220988263222226542297393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3255968701925937446126381 1220988263222226542297393)
  ·
    refine ⟨915741197416669906723045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1220988263222226542297393 915741197416669906723045)
    ·
      refine ⟨171701474515625607510571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 915741197416669906723045 171701474515625607510571)
      ·
        refine ⟨257552211773438411265857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171701474515625607510571 257552211773438411265857)
        ·
          refine ⟨193164158830078808449393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257552211773438411265857 193164158830078808449393)
          ·
            refine ⟨144873119122559106337045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193164158830078808449393 144873119122559106337045)
            ·
              refine ⟨6790927458869958109549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144873119122559106337045 6790927458869958109549)
              ·
                rfl

theorem cell20_133906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 6].length) (baseStart_133906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133906 prefixEnd_133906 := by exact prefixLift 133906
  have htrace : WordTrace (prefixWord ++ tailWord_133906) baseStart_133906 baseEnd_133906 := by
    simpa [prefixWord, tailWord_133906, baseEnd_133906] using wordTrace_append hprefix tailTrace_133906
  have hstable : (prefixWord ++ tailWord_133906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133906).length < 2 ^ (prefixWord ++ tailWord_133906).sum := by decide
  have hdescent : baseEnd_133906 < baseStart_133906 := by decide
  rcases family_descends (prefixWord ++ tailWord_133906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133920 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 4]
def baseStart_133920 : Nat := 118140960795 + 133920 * 2 ^ 59
def prefixEnd_133920 : Nat := 4983230072969 + 3 ^ 40 * 133920 * 2
def baseEnd_133920 : Nat := 61124737111307796519217

theorem tailTrace_133920 : CollatzResearch.WordTrace tailWord_133920 prefixEnd_133920 61124737111307796519217 := by
  unfold tailWord_133920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2442231837419093280099607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3256309116558791040132809 2442231837419093280099607)
  ·
    refine ⟨3663347756128639920149411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2442231837419093280099607 3663347756128639920149411)
    ·
      refine ⟨5495021634192959880224117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3663347756128639920149411 5495021634192959880224117)
      ·
        refine ⟨515158278205589988771011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5495021634192959880224117 515158278205589988771011)
        ·
          refine ⟨772737417308384983156517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515158278205589988771011 772737417308384983156517)
          ·
            refine ⟨144888265745322184341847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 772737417308384983156517 144888265745322184341847)
            ·
              refine ⟨217332398617983276512771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144888265745322184341847 217332398617983276512771)
              ·
                refine ⟨325998597926974914769157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217332398617983276512771 325998597926974914769157)
                ·
                  refine ⟨61124737111307796519217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325998597926974914769157 61124737111307796519217)
                  ·
                    rfl

theorem cell20_133920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_133920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133920 prefixEnd_133920 := by exact prefixLift 133920
  have htrace : WordTrace (prefixWord ++ tailWord_133920) baseStart_133920 baseEnd_133920 := by
    simpa [prefixWord, tailWord_133920, baseEnd_133920] using wordTrace_append hprefix tailTrace_133920
  have hstable : (prefixWord ++ tailWord_133920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133920).length < 2 ^ (prefixWord ++ tailWord_133920).sum := by decide
  have hdescent : baseEnd_133920 < baseStart_133920 := by decide
  rcases family_descends (prefixWord ++ tailWord_133920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133930 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_133930 : Nat := 118140960795 + 133930 * 2 ^ 59
def prefixEnd_133930 : Nat := 4983230072969 + 3 ^ 40 * 133930 * 2
def baseEnd_133930 : Nat := 61129301383792206185843

theorem tailTrace_133930 : CollatzResearch.WordTrace tailWord_133930 prefixEnd_133930 61129301383792206185843 := by
  unfold tailWord_133930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1221207101200489567015811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3256552269867972178708829 1221207101200489567015811)
  ·
    refine ⟨1831810651800734350523717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1221207101200489567015811 1831810651800734350523717)
    ·
      refine ⟨343464497212637690723197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1831810651800734350523717 343464497212637690723197)
      ·
        refine ⟨128799186454739134021199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343464497212637690723197 128799186454739134021199)
        ·
          refine ⟨193198779682108701031799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128799186454739134021199 193198779682108701031799)
          ·
            refine ⟨289798169523163051547699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193198779682108701031799 289798169523163051547699)
            ·
              refine ⟨434697254284744577321549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289798169523163051547699 434697254284744577321549)
              ·
                refine ⟨163011470356779216495581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434697254284744577321549 163011470356779216495581)
                ·
                  refine ⟨61129301383792206185843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163011470356779216495581 61129301383792206185843)
                  ·
                    rfl

theorem cell20_133930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_133930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133930 prefixEnd_133930 := by exact prefixLift 133930
  have htrace : WordTrace (prefixWord ++ tailWord_133930) baseStart_133930 baseEnd_133930 := by
    simpa [prefixWord, tailWord_133930, baseEnd_133930] using wordTrace_append hprefix tailTrace_133930
  have hstable : (prefixWord ++ tailWord_133930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133930).length < 2 ^ (prefixWord ++ tailWord_133930).sum := by decide
  have hdescent : baseEnd_133930 < baseStart_133930 := by decide
  rcases family_descends (prefixWord ++ tailWord_133930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133931 : List Nat := [1, 1, 1, 1, 2, 1, 2, 11]
def baseStart_133931 : Nat := 118140960795 + 133931 * 2 ^ 59
def prefixEnd_133931 : Nat := 4983230072969 + 3 ^ 40 * 133931 * 2
def baseEnd_133931 : Nat := 20376585937013549050835

theorem tailTrace_133931 : CollatzResearch.WordTrace tailWord_133931 prefixEnd_133931 20376585937013549050835 := by
  unfold tailWord_133931
  simp only [CollatzResearch.WordTrace]
  refine ⟨4884864877798335438849647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3256576585198890292566431 4884864877798335438849647)
  ·
    refine ⟨7327297316697503158274471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4884864877798335438849647 7327297316697503158274471)
    ·
      refine ⟨10990945975046254737411707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7327297316697503158274471 10990945975046254737411707)
      ·
        refine ⟨16486418962569382106117561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10990945975046254737411707 16486418962569382106117561)
        ·
          refine ⟨12364814221927036579588171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16486418962569382106117561 12364814221927036579588171)
          ·
            refine ⟨18547221332890554869382257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12364814221927036579588171 18547221332890554869382257)
            ·
              refine ⟨13910415999667916152036693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18547221332890554869382257 13910415999667916152036693)
              ·
                refine ⟨20376585937013549050835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 13910415999667916152036693 20376585937013549050835)
                ·
                  rfl

theorem cell20_133931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_133931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133931 prefixEnd_133931 := by exact prefixLift 133931
  have htrace : WordTrace (prefixWord ++ tailWord_133931) baseStart_133931 baseEnd_133931 := by
    simpa [prefixWord, tailWord_133931, baseEnd_133931] using wordTrace_append hprefix tailTrace_133931
  have hstable : (prefixWord ++ tailWord_133931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133931).length < 2 ^ (prefixWord ++ tailWord_133931).sum := by decide
  have hdescent : baseEnd_133931 < baseStart_133931 := by decide
  rcases family_descends (prefixWord ++ tailWord_133931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133962 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 8]
def baseStart_133962 : Nat := 118140960795 + 133962 * 2 ^ 59
def prefixEnd_133962 : Nat := 4983230072969 + 3 ^ 40 * 133962 * 2
def baseEnd_133962 : Nat := 61143907055742317119045

theorem tailTrace_133962 : CollatzResearch.WordTrace tailWord_133962 prefixEnd_133962 61143907055742317119045 := by
  unfold tailWord_133962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1221498885171506933307035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3257330360457351822152093 1221498885171506933307035)
  ·
    refine ⟨1832248327757260399960553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1221498885171506933307035 1832248327757260399960553)
    ·
      refine ⟨1374186245817945299970415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1832248327757260399960553 1374186245817945299970415)
      ·
        refine ⟨2061279368726917949955623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374186245817945299970415 2061279368726917949955623)
        ·
          refine ⟨3091919053090376924933435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061279368726917949955623 3091919053090376924933435)
          ·
            refine ⟨4637878579635565387400153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3091919053090376924933435 4637878579635565387400153)
            ·
              refine ⟨3478408934726674040550115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4637878579635565387400153 3478408934726674040550115)
              ·
                refine ⟨5217613402090011060825173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478408934726674040550115 5217613402090011060825173)
                ·
                  refine ⟨61143907055742317119045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5217613402090011060825173 61143907055742317119045)
                  ·
                    rfl

theorem cell20_133962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_133962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133962 prefixEnd_133962 := by exact prefixLift 133962
  have htrace : WordTrace (prefixWord ++ tailWord_133962) baseStart_133962 baseEnd_133962 := by
    simpa [prefixWord, tailWord_133962, baseEnd_133962] using wordTrace_append hprefix tailTrace_133962
  have hstable : (prefixWord ++ tailWord_133962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133962).length < 2 ^ (prefixWord ++ tailWord_133962).sum := by decide
  have hdescent : baseEnd_133962 < baseStart_133962 := by decide
  rcases family_descends (prefixWord ++ tailWord_133962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133965 : List Nat := [1, 6, 1, 2, 2, 8]
def baseStart_133965 : Nat := 118140960795 + 133965 * 2 ^ 59
def prefixEnd_133965 : Nat := 4983230072969 + 3 ^ 40 * 133965 * 2
def baseEnd_133965 : Nat := 2264639864351394074779

theorem tailTrace_133965 : CollatzResearch.WordTrace tailWord_133965 prefixEnd_133965 2264639864351394074779 := by
  unfold tailWord_133965
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886104959675159245587349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3257403306450106163724899 4886104959675159245587349)
  ·
    refine ⟨229036169984773089636907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4886104959675159245587349 229036169984773089636907)
    ·
      refine ⟨343554254977159634455361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229036169984773089636907 343554254977159634455361)
      ·
        refine ⟨257665691232869725841521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343554254977159634455361 257665691232869725841521)
        ·
          refine ⟨193249268424652294381141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257665691232869725841521 193249268424652294381141)
          ·
            refine ⟨2264639864351394074779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 193249268424652294381141 2264639864351394074779)
            ·
              rfl

theorem cell20_133965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 8].length) (baseStart_133965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133965 prefixEnd_133965 := by exact prefixLift 133965
  have htrace : WordTrace (prefixWord ++ tailWord_133965) baseStart_133965 baseEnd_133965 := by
    simpa [prefixWord, tailWord_133965, baseEnd_133965] using wordTrace_append hprefix tailTrace_133965
  have hstable : (prefixWord ++ tailWord_133965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133965).length < 2 ^ (prefixWord ++ tailWord_133965).sum := by decide
  have hdescent : baseEnd_133965 < baseStart_133965 := by decide
  rcases family_descends (prefixWord ++ tailWord_133965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133969 : List Nat := [1, 2, 2, 1, 14]
def baseStart_133969 : Nat := 118140960795 + 133969 * 2 ^ 59
def prefixEnd_133969 : Nat := 4983230072969 + 3 ^ 40 * 133969 * 2
def baseEnd_133969 : Nat := 754902494401004986243

theorem tailTrace_133969 : CollatzResearch.WordTrace tailWord_133969 prefixEnd_133969 754902494401004986243 := by
  unfold tailWord_133969
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886250851660667928732961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3257500567773778619155307 4886250851660667928732961)
  ·
    refine ⟨3664688138745500946549721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4886250851660667928732961 3664688138745500946549721)
    ·
      refine ⟨2748516104059125709912291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3664688138745500946549721 2748516104059125709912291)
      ·
        refine ⟨4122774156088688564868437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2748516104059125709912291 4122774156088688564868437)
        ·
          refine ⟨754902494401004986243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 4122774156088688564868437 754902494401004986243)
          ·
            rfl

theorem cell20_133969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 14].length) (baseStart_133969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133969 prefixEnd_133969 := by exact prefixLift 133969
  have htrace : WordTrace (prefixWord ++ tailWord_133969) baseStart_133969 baseEnd_133969 := by
    simpa [prefixWord, tailWord_133969, baseEnd_133969] using wordTrace_append hprefix tailTrace_133969
  have hstable : (prefixWord ++ tailWord_133969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133969).length < 2 ^ (prefixWord ++ tailWord_133969).sum := by decide
  have hdescent : baseEnd_133969 < baseStart_133969 := by decide
  rcases family_descends (prefixWord ++ tailWord_133969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133975 : List Nat := [1, 1, 3, 2, 4, 1, 4, 2, 2]
def baseStart_133975 : Nat := 118140960795 + 133975 * 2 ^ 59
def prefixEnd_133975 : Nat := 4983230072969 + 3 ^ 40 * 133975 * 2
def baseEnd_133975 : Nat := 61149840609972049685659

theorem tailTrace_133975 : CollatzResearch.WordTrace tailWord_133975 prefixEnd_133975 61149840609972049685659 := by
  unfold tailWord_133975
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886469689638930953451379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3257646459759287302300919 4886469689638930953451379)
  ·
    refine ⟨7329704534458396430177069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4886469689638930953451379 7329704534458396430177069)
    ·
      refine ⟨2748639200421898661316401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7329704534458396430177069 2748639200421898661316401)
      ·
        refine ⟨2061479400316423995987301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2748639200421898661316401 2061479400316423995987301)
        ·
          refine ⟨386527387559329499247619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2061479400316423995987301 386527387559329499247619)
          ·
            refine ⟨579791081338994248871429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386527387559329499247619 579791081338994248871429)
            ·
              refine ⟨108710827751061421663393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 579791081338994248871429 108710827751061421663393)
              ·
                refine ⟨81533120813296066247545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108710827751061421663393 81533120813296066247545)
                ·
                  refine ⟨61149840609972049685659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81533120813296066247545 61149840609972049685659)
                  ·
                    rfl

theorem cell20_133975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 2].length) (baseStart_133975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_133975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_133975 prefixEnd_133975 := by exact prefixLift 133975
  have htrace : WordTrace (prefixWord ++ tailWord_133975) baseStart_133975 baseEnd_133975 := by
    simpa [prefixWord, tailWord_133975, baseEnd_133975] using wordTrace_append hprefix tailTrace_133975
  have hstable : (prefixWord ++ tailWord_133975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133975).length < 2 ^ (prefixWord ++ tailWord_133975).sum := by decide
  have hdescent : baseEnd_133975 < baseStart_133975 := by decide
  rcases family_descends (prefixWord ++ tailWord_133975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134000 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_134000 : Nat := 118140960795 + 134000 * 2 ^ 59
def prefixEnd_134000 : Nat := 4983230072969 + 3 ^ 40 * 134000 * 2
def baseEnd_134000 : Nat := 61161251291183073852223

theorem tailTrace_134000 : CollatzResearch.WordTrace tailWord_134000 prefixEnd_134000 61161251291183073852223 := by
  unfold tailWord_134000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2443690757274180111555727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3258254343032240148740969 2443690757274180111555727)
  ·
    refine ⟨3665536135911270167333591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2443690757274180111555727 3665536135911270167333591)
    ·
      refine ⟨5498304203866905251000387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3665536135911270167333591 5498304203866905251000387)
      ·
        refine ⟨8247456305800357876500581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5498304203866905251000387 8247456305800357876500581)
        ·
          refine ⟨1546398057337567101843859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8247456305800357876500581 1546398057337567101843859)
          ·
            refine ⟨2319597086006350652765789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546398057337567101843859 2319597086006350652765789)
            ·
              refine ⟨869848907252381494787171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2319597086006350652765789 869848907252381494787171)
              ·
                refine ⟨1304773360878572242180757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869848907252381494787171 1304773360878572242180757)
                ·
                  refine ⟨61161251291183073852223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1304773360878572242180757 61161251291183073852223)
                  ·
                    rfl

theorem cell20_134000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_134000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134000 prefixEnd_134000 := by exact prefixLift 134000
  have htrace : WordTrace (prefixWord ++ tailWord_134000) baseStart_134000 baseEnd_134000 := by
    simpa [prefixWord, tailWord_134000, baseEnd_134000] using wordTrace_append hprefix tailTrace_134000
  have hstable : (prefixWord ++ tailWord_134000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134000).length < 2 ^ (prefixWord ++ tailWord_134000).sum := by decide
  have hdescent : baseEnd_134000 < baseStart_134000 := by decide
  rcases family_descends (prefixWord ++ tailWord_134000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134007 : List Nat := [1, 1, 3, 1, 1, 2, 1, 10]
def baseStart_134007 : Nat := 118140960795 + 134007 * 2 ^ 59
def prefixEnd_134007 : Nat := 4983230072969 + 3 ^ 40 * 134007 * 2
def baseEnd_134007 : Nat := 20388148760640720206287

theorem tailTrace_134007 : CollatzResearch.WordTrace tailWord_134007 prefixEnd_134007 20388148760640720206287 := by
  unfold tailWord_134007
  simp only [CollatzResearch.WordTrace]
  refine ⟨4887636825523000418616275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3258424550348666945744183 4887636825523000418616275)
  ·
    refine ⟨7331455238284500627924413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4887636825523000418616275 7331455238284500627924413)
    ·
      refine ⟨2749295714356687735471655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7331455238284500627924413 2749295714356687735471655)
      ·
        refine ⟨4123943571535031603207483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2749295714356687735471655 4123943571535031603207483)
        ·
          refine ⟨6185915357302547404811225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4123943571535031603207483 6185915357302547404811225)
          ·
            refine ⟨4639436517976910553608419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6185915357302547404811225 4639436517976910553608419)
            ·
              refine ⟨6959154776965365830412629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4639436517976910553608419 6959154776965365830412629)
              ·
                refine ⟨20388148760640720206287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6959154776965365830412629 20388148760640720206287)
                ·
                  rfl

theorem cell20_134007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 10].length) (baseStart_134007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134007 prefixEnd_134007 := by exact prefixLift 134007
  have htrace : WordTrace (prefixWord ++ tailWord_134007) baseStart_134007 baseEnd_134007 := by
    simpa [prefixWord, tailWord_134007, baseEnd_134007] using wordTrace_append hprefix tailTrace_134007
  have hstable : (prefixWord ++ tailWord_134007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134007).length < 2 ^ (prefixWord ++ tailWord_134007).sum := by decide
  have hdescent : baseEnd_134007 < baseStart_134007 := by decide
  rcases family_descends (prefixWord ++ tailWord_134007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134024 : List Nat := [2, 1, 3, 3, 2, 2, 7]
def baseStart_134024 : Nat := 118140960795 + 134024 * 2 ^ 59
def prefixEnd_134024 : Nat := 4983230072969 + 3 ^ 40 * 134024 * 2
def baseEnd_134024 : Nat := 6796911727238406339125

theorem tailTrace_134024 : CollatzResearch.WordTrace tailWord_134024 prefixEnd_134024 6796911727238406339125 := by
  unfold tailWord_134024
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444128433230706160992563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3258837910974274881323417 2444128433230706160992563)
  ·
    refine ⟨3666192649846059241488845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2444128433230706160992563 3666192649846059241488845)
    ·
      refine ⟨1374822243692272215558317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3666192649846059241488845 1374822243692272215558317)
      ·
        refine ⟨515558341384602080834369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1374822243692272215558317 515558341384602080834369)
        ·
          refine ⟨386668756038451560625777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515558341384602080834369 386668756038451560625777)
          ·
            refine ⟨290001567028838670469333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386668756038451560625777 290001567028838670469333)
            ·
              refine ⟨6796911727238406339125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 290001567028838670469333 6796911727238406339125)
              ·
                rfl

theorem cell20_134024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 7].length) (baseStart_134024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134024 prefixEnd_134024 := by exact prefixLift 134024
  have htrace : WordTrace (prefixWord ++ tailWord_134024) baseStart_134024 baseEnd_134024 := by
    simpa [prefixWord, tailWord_134024, baseEnd_134024] using wordTrace_append hprefix tailTrace_134024
  have hstable : (prefixWord ++ tailWord_134024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134024).length < 2 ^ (prefixWord ++ tailWord_134024).sum := by decide
  have hdescent : baseEnd_134024 < baseStart_134024 := by decide
  rcases family_descends (prefixWord ++ tailWord_134024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134044 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 3]
def baseStart_134044 : Nat := 118140960795 + 134044 * 2 ^ 59
def prefixEnd_134044 : Nat := 4983230072969 + 3 ^ 40 * 134044 * 2
def baseEnd_134044 : Nat := 61181334090114476385377

theorem tailTrace_134044 : CollatzResearch.WordTrace tailWord_134044 prefixEnd_134044 61181334090114476385377 := by
  unfold tailWord_134044
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444493163194477868856593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3259324217592637158475457 2444493163194477868856593)
  ·
    refine ⟨1833369872395858401642445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2444493163194477868856593 1833369872395858401642445)
    ·
      refine ⟨687513702148446900615917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1833369872395858401642445 687513702148446900615917)
      ·
        refine ⟨257817638305667587730969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 687513702148446900615917 257817638305667587730969)
        ·
          refine ⟨193363228729250690798227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257817638305667587730969 193363228729250690798227)
          ·
            refine ⟨290044843093876036197341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193363228729250690798227 290044843093876036197341)
            ·
              refine ⟨108766816160203513574003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290044843093876036197341 108766816160203513574003)
              ·
                refine ⟨163150224240305270361005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108766816160203513574003 163150224240305270361005)
                ·
                  refine ⟨61181334090114476385377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163150224240305270361005 61181334090114476385377)
                  ·
                    rfl

theorem cell20_134044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_134044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134044 prefixEnd_134044 := by exact prefixLift 134044
  have htrace : WordTrace (prefixWord ++ tailWord_134044) baseStart_134044 baseEnd_134044 := by
    simpa [prefixWord, tailWord_134044, baseEnd_134044] using wordTrace_append hprefix tailTrace_134044
  have hstable : (prefixWord ++ tailWord_134044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134044).length < 2 ^ (prefixWord ++ tailWord_134044).sum := by decide
  have hdescent : baseEnd_134044 < baseStart_134044 := by decide
  rcases family_descends (prefixWord ++ tailWord_134044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134068 : List Nat := [2, 5, 2, 1, 1, 1, 3, 3, 2]
def baseStart_134068 : Nat := 118140960795 + 134068 * 2 ^ 59
def prefixEnd_134068 : Nat := 4983230072969 + 3 ^ 40 * 134068 * 2
def baseEnd_134068 : Nat := 61192288344077059585279

theorem tailTrace_134068 : CollatzResearch.WordTrace tailWord_134068 prefixEnd_134068 61192288344077059585279 := by
  unfold tailWord_134068
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444930839151003918293429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3259907785534671891057905 2444930839151003918293429)
  ·
    refine ⟨229212266170406617340009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2444930839151003918293429 229212266170406617340009)
    ·
      refine ⟨171909199627804963005007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229212266170406617340009 171909199627804963005007)
      ·
        refine ⟨257863799441707444507511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171909199627804963005007 257863799441707444507511)
        ·
          refine ⟨386795699162561166761267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257863799441707444507511 386795699162561166761267)
          ·
            refine ⟨580193548743841750141901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386795699162561166761267 580193548743841750141901)
            ·
              refine ⟨217572580778940656303213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580193548743841750141901 217572580778940656303213)
              ·
                refine ⟨81589717792102746113705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217572580778940656303213 81589717792102746113705)
                ·
                  refine ⟨61192288344077059585279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81589717792102746113705 61192288344077059585279)
                  ·
                    rfl

theorem cell20_134068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_134068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134068 prefixEnd_134068 := by exact prefixLift 134068
  have htrace : WordTrace (prefixWord ++ tailWord_134068) baseStart_134068 baseEnd_134068 := by
    simpa [prefixWord, tailWord_134068, baseEnd_134068] using wordTrace_append hprefix tailTrace_134068
  have hstable : (prefixWord ++ tailWord_134068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134068).length < 2 ^ (prefixWord ++ tailWord_134068).sum := by decide
  have hdescent : baseEnd_134068 < baseStart_134068 := by decide
  rcases family_descends (prefixWord ++ tailWord_134068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134069 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_134069 : Nat := 118140960795 + 134069 * 2 ^ 59
def prefixEnd_134069 : Nat := 4983230072969 + 3 ^ 40 * 134069 * 2
def baseEnd_134069 : Nat := 61192744771325500551941

theorem tailTrace_134069 : CollatzResearch.WordTrace tailWord_134069 prefixEnd_134069 61192744771325500551941 := by
  unfold tailWord_134069
  simp only [CollatzResearch.WordTrace]
  refine ⟨4889898151298385007373261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3259932100865590004915507 4889898151298385007373261)
  ·
    refine ⟨1833711806736894377764973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4889898151298385007373261 1833711806736894377764973)
    ·
      refine ⟨687641927526335391661865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1833711806736894377764973 687641927526335391661865)
      ·
        refine ⟨515731445644751543746399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687641927526335391661865 515731445644751543746399)
        ·
          refine ⟨773597168467127315619599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515731445644751543746399 773597168467127315619599)
          ·
            refine ⟨1160395752700690973429399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773597168467127315619599 1160395752700690973429399)
            ·
              refine ⟨1740593629051036460144099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160395752700690973429399 1740593629051036460144099)
              ·
                refine ⟨2610890443576554690216149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740593629051036460144099 2610890443576554690216149)
                ·
                  refine ⟨61192744771325500551941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2610890443576554690216149 61192744771325500551941)
                  ·
                    rfl

theorem cell20_134069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_134069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134069 prefixEnd_134069 := by exact prefixLift 134069
  have htrace : WordTrace (prefixWord ++ tailWord_134069) baseStart_134069 baseEnd_134069 := by
    simpa [prefixWord, tailWord_134069, baseEnd_134069] using wordTrace_append hprefix tailTrace_134069
  have hstable : (prefixWord ++ tailWord_134069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134069).length < 2 ^ (prefixWord ++ tailWord_134069).sum := by decide
  have hdescent : baseEnd_134069 < baseStart_134069 := by decide
  rcases family_descends (prefixWord ++ tailWord_134069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134072 : List Nat := [2, 1, 2, 1, 2, 4, 3, 3, 2]
def baseStart_134072 : Nat := 118140960795 + 134072 * 2 ^ 59
def prefixEnd_134072 : Nat := 4983230072969 + 3 ^ 40 * 134072 * 2
def baseEnd_134072 : Nat := 61194114053070823451929

theorem tailTrace_134072 : CollatzResearch.WordTrace tailWord_134072 prefixEnd_134072 61194114053070823451929 := by
  unfold tailWord_134072
  simp only [CollatzResearch.WordTrace]
  refine ⟨2445003785143758259866235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3260005046858344346488313 2445003785143758259866235)
  ·
    refine ⟨3667505677715637389799353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2445003785143758259866235 3667505677715637389799353)
    ·
      refine ⟨2750629258286728042349515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3667505677715637389799353 2750629258286728042349515)
      ·
        refine ⟨4125943887430092063524273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2750629258286728042349515 4125943887430092063524273)
        ·
          refine ⟨3094457915572569047643205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4125943887430092063524273 3094457915572569047643205)
          ·
            refine ⟨580210859169856696433101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3094457915572569047643205 580210859169856696433101)
            ·
              refine ⟨217579072188696261162413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580210859169856696433101 217579072188696261162413)
              ·
                refine ⟨81592152070761097935905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217579072188696261162413 81592152070761097935905)
                ·
                  refine ⟨61194114053070823451929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81592152070761097935905 61194114053070823451929)
                  ·
                    rfl

theorem cell20_134072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_134072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134072 prefixEnd_134072 := by exact prefixLift 134072
  have htrace : WordTrace (prefixWord ++ tailWord_134072) baseStart_134072 baseEnd_134072 := by
    simpa [prefixWord, tailWord_134072, baseEnd_134072] using wordTrace_append hprefix tailTrace_134072
  have hstable : (prefixWord ++ tailWord_134072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134072).length < 2 ^ (prefixWord ++ tailWord_134072).sum := by decide
  have hdescent : baseEnd_134072 < baseStart_134072 := by decide
  rcases family_descends (prefixWord ++ tailWord_134072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
