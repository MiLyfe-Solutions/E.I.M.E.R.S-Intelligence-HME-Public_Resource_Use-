import V185TrunkScan22Chunk136

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1226080 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_1226080 : Nat := 118140960795 + 1226080 * 2 ^ 59
def prefixEnd_1226080 : Nat := 4983230072969 + 3 ^ 40 * 1226080 * 2
def baseEnd_1226080 : Nat := 419712240576445460040911

theorem tailTrace_1226080 : CollatzResearch.WordTrace tailWord_1226080 prefixEnd_1226080 419712240576445460040911 := by
  unfold tailWord_1226080
  simp only [CollatzResearch.WordTrace]
  refine ⟨22359405699064516319049847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29812540932086021758733129 22359405699064516319049847)
  ·
    refine ⟨33539108548596774478574771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22359405699064516319049847 33539108548596774478574771)
    ·
      refine ⟨50308662822895161717862157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33539108548596774478574771 50308662822895161717862157)
      ·
        refine ⟨18865748558585685644198309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50308662822895161717862157 18865748558585685644198309)
        ·
          refine ⟨3537327854734816058287183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18865748558585685644198309 3537327854734816058287183)
          ·
            refine ⟨5305991782102224087430775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537327854734816058287183 5305991782102224087430775)
            ·
              refine ⟨7958987673153336131146163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5305991782102224087430775 7958987673153336131146163)
              ·
                refine ⟨11938481509730004196719245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7958987673153336131146163 11938481509730004196719245)
                ·
                  refine ⟨4476930566148751573769717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11938481509730004196719245 4476930566148751573769717)
                  ·
                    refine ⟨419712240576445460040911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4476930566148751573769717 419712240576445460040911)
                    ·
                      rfl

theorem cell22_1226080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_1226080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226080 prefixEnd_1226080 := by exact prefixLift 1226080
  have htrace : WordTrace (prefixWord ++ tailWord_1226080) baseStart_1226080 baseEnd_1226080 := by
    simpa [prefixWord, tailWord_1226080, baseEnd_1226080] using wordTrace_append hprefix tailTrace_1226080
  have hstable : (prefixWord ++ tailWord_1226080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226080).length < 2 ^ (prefixWord ++ tailWord_1226080).sum := by decide
  have hdescent : baseEnd_1226080 < baseStart_1226080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226084 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_1226084 : Nat := 118140960795 + 1226084 * 2 ^ 59
def prefixEnd_1226084 : Nat := 4983230072969 + 3 ^ 40 * 1226084 * 2
def baseEnd_1226084 : Nat := 419713609858190782940899

theorem tailTrace_1226084 : CollatzResearch.WordTrace tailWord_1226084 prefixEnd_1226084 419713609858190782940899 := by
  unfold tailWord_1226084
  simp only [CollatzResearch.WordTrace]
  refine ⟨22359478645057270660622653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29812638193409694214163537 22359478645057270660622653)
  ·
    refine ⟨8384804491896476497733495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22359478645057270660622653 8384804491896476497733495)
    ·
      refine ⟨12577206737844714746600243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8384804491896476497733495 12577206737844714746600243)
      ·
        refine ⟨18865810106767072119900365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12577206737844714746600243 18865810106767072119900365)
        ·
          refine ⟨7074678790037652044962637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18865810106767072119900365 7074678790037652044962637)
          ·
            refine ⟨2653004546264119516860989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7074678790037652044962637 2653004546264119516860989)
            ·
              refine ⟨994876704849044818822871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2653004546264119516860989 994876704849044818822871)
              ·
                refine ⟨1492315057273567228234307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994876704849044818822871 1492315057273567228234307)
                ·
                  refine ⟨2238472585910350842351461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492315057273567228234307 2238472585910350842351461)
                  ·
                    refine ⟨419713609858190782940899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238472585910350842351461 419713609858190782940899)
                    ·
                      rfl

theorem cell22_1226084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_1226084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226084 prefixEnd_1226084 := by exact prefixLift 1226084
  have htrace : WordTrace (prefixWord ++ tailWord_1226084) baseStart_1226084 baseEnd_1226084 := by
    simpa [prefixWord, tailWord_1226084, baseEnd_1226084] using wordTrace_append hprefix tailTrace_1226084
  have hstable : (prefixWord ++ tailWord_1226084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226084).length < 2 ^ (prefixWord ++ tailWord_1226084).sum := by decide
  have hdescent : baseEnd_1226084 < baseStart_1226084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226095 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 2, 4]
def baseStart_1226095 : Nat := 118140960795 + 1226095 * 2 ^ 59
def prefixEnd_1226095 : Nat := 4983230072969 + 3 ^ 40 * 1226095 * 2
def baseEnd_1226095 : Nat := 419717375382990420915865

theorem tailTrace_1226095 : CollatzResearch.WordTrace tailWord_1226095 prefixEnd_1226095 419717375382990420915865 := by
  unfold tailWord_1226095
  simp only [CollatzResearch.WordTrace]
  refine ⟨44719358493074690199895739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29812905662049793466597159 44719358493074690199895739)
  ·
    refine ⟨67079037739612035299843609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44719358493074690199895739 67079037739612035299843609)
    ·
      refine ⟨50309278304709026474882707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67079037739612035299843609 50309278304709026474882707)
      ·
        refine ⟨75463917457063539712324061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50309278304709026474882707 75463917457063539712324061)
        ·
          refine ⟨28298969046398827392121523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75463917457063539712324061 28298969046398827392121523)
          ·
            refine ⟨42448453569598241088182285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28298969046398827392121523 42448453569598241088182285)
            ·
              refine ⟨15918170088599340408068357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42448453569598241088182285 15918170088599340408068357)
              ·
                refine ⟨2984656891612376326512817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15918170088599340408068357 2984656891612376326512817)
                ·
                  refine ⟨2238492668709282244884613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2984656891612376326512817 2238492668709282244884613)
                  ·
                    refine ⟨419717375382990420915865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238492668709282244884613 419717375382990420915865)
                    ·
                      rfl

theorem cell22_1226095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_1226095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226095 prefixEnd_1226095 := by exact prefixLift 1226095
  have htrace : WordTrace (prefixWord ++ tailWord_1226095) baseStart_1226095 baseEnd_1226095 := by
    simpa [prefixWord, tailWord_1226095, baseEnd_1226095] using wordTrace_append hprefix tailTrace_1226095
  have hstable : (prefixWord ++ tailWord_1226095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226095).length < 2 ^ (prefixWord ++ tailWord_1226095).sum := by decide
  have hdescent : baseEnd_1226095 < baseStart_1226095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226097 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 2, 3]
def baseStart_1226097 : Nat := 118140960795 + 1226097 * 2 ^ 59
def prefixEnd_1226097 : Nat := 4983230072969 + 3 ^ 40 * 1226097 * 2
def baseEnd_1226097 : Nat := 419718060023863082365859

theorem tailTrace_1226097 : CollatzResearch.WordTrace tailWord_1226097 prefixEnd_1226097 419718060023863082365859 := by
  unfold tailWord_1226097
  simp only [CollatzResearch.WordTrace]
  refine ⟨44719431439067444541468545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29812954292711629694312363 44719431439067444541468545)
  ·
    refine ⟨33539573579300583406101409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44719431439067444541468545 33539573579300583406101409)
    ·
      refine ⟨25154680184475437554576057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33539573579300583406101409 25154680184475437554576057)
      ·
        refine ⟨18866010138356578165932043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25154680184475437554576057 18866010138356578165932043)
        ·
          refine ⟨28299015207534867248898065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18866010138356578165932043 28299015207534867248898065)
          ·
            refine ⟨21224261405651150436673549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28299015207534867248898065 21224261405651150436673549)
            ·
              refine ⟨7959098027119181413752581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21224261405651150436673549 7959098027119181413752581)
              ·
                refine ⟨1492330880084846515078609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7959098027119181413752581 1492330880084846515078609)
                ·
                  refine ⟨1119248160063634886308957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1492330880084846515078609 1119248160063634886308957)
                  ·
                    refine ⟨419718060023863082365859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1119248160063634886308957 419718060023863082365859)
                    ·
                      rfl

theorem cell22_1226097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_1226097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226097 prefixEnd_1226097 := by exact prefixLift 1226097
  have htrace : WordTrace (prefixWord ++ tailWord_1226097) baseStart_1226097 baseEnd_1226097 := by
    simpa [prefixWord, tailWord_1226097, baseEnd_1226097] using wordTrace_append hprefix tailTrace_1226097
  have hstable : (prefixWord ++ tailWord_1226097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226097).length < 2 ^ (prefixWord ++ tailWord_1226097).sum := by decide
  have hdescent : baseEnd_1226097 < baseStart_1226097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226114 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1226114 : Nat := 118140960795 + 1226114 * 2 ^ 59
def prefixEnd_1226114 : Nat := 4983230072969 + 3 ^ 40 * 1226114 * 2
def baseEnd_1226114 : Nat := 419723879471280704690807

theorem tailTrace_1226114 : CollatzResearch.WordTrace tailWord_1226114 prefixEnd_1226114 419723879471280704690807 := by
  unfold tailWord_1226114
  simp only [CollatzResearch.WordTrace]
  refine ⟨11180012870001464111209349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29813367653337237629891597 11180012870001464111209349)
  ·
    refine ⟨2096252413125274520851753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11180012870001464111209349 2096252413125274520851753)
    ·
      refine ⟨1572189309843955890638815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2096252413125274520851753 1572189309843955890638815)
      ·
        refine ⟨2358283964765933835958223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572189309843955890638815 2358283964765933835958223)
        ·
          refine ⟨3537425947148900753937335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358283964765933835958223 3537425947148900753937335)
          ·
            refine ⟨5306138920723351130906003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537425947148900753937335 5306138920723351130906003)
            ·
              refine ⟨7959208381085026696359005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5306138920723351130906003 7959208381085026696359005)
              ·
                refine ⟨2984703142906885011134627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7959208381085026696359005 2984703142906885011134627)
                ·
                  refine ⟨4477054714360327516701941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984703142906885011134627 4477054714360327516701941)
                  ·
                    refine ⟨419723879471280704690807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4477054714360327516701941 419723879471280704690807)
                    ·
                      rfl

theorem cell22_1226114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1226114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226114 prefixEnd_1226114 := by exact prefixLift 1226114
  have htrace : WordTrace (prefixWord ++ tailWord_1226114) baseStart_1226114 baseEnd_1226114 := by
    simpa [prefixWord, tailWord_1226114, baseEnd_1226114] using wordTrace_append hprefix tailTrace_1226114
  have hstable : (prefixWord ++ tailWord_1226114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226114).length < 2 ^ (prefixWord ++ tailWord_1226114).sum := by decide
  have hdescent : baseEnd_1226114 < baseStart_1226114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226178 : List Nat := [3, 5, 2, 1, 1, 1, 1, 8]
def baseStart_1226178 : Nat := 118140960795 + 1226178 * 2 ^ 59
def prefixEnd_1226178 : Nat := 4983230072969 + 3 ^ 40 * 1226178 * 2
def baseEnd_1226178 : Nat := 46638420886578430121179

theorem tailTrace_1226178 : CollatzResearch.WordTrace tailWord_1226178 prefixEnd_1226178 46638420886578430121179 := by
  unfold tailWord_1226178
  simp only [CollatzResearch.WordTrace]
  refine ⟨11180596437943498843791797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29814923834515996916778125 11180596437943498843791797)
  ·
    refine ⟨1048180916057203016605481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11180596437943498843791797 1048180916057203016605481)
    ·
      refine ⟨786135687042902262454111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1048180916057203016605481 786135687042902262454111)
      ·
        refine ⟨1179203530564353393681167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786135687042902262454111 1179203530564353393681167)
        ·
          refine ⟨1768805295846530090521751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179203530564353393681167 1768805295846530090521751)
          ·
            refine ⟨2653207943769795135782627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768805295846530090521751 2653207943769795135782627)
            ·
              refine ⟨3979811915654692703673941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653207943769795135782627 3979811915654692703673941)
              ·
                refine ⟨46638420886578430121179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3979811915654692703673941 46638420886578430121179)
                ·
                  rfl

theorem cell22_1226178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_1226178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226178 prefixEnd_1226178 := by exact prefixLift 1226178
  have htrace : WordTrace (prefixWord ++ tailWord_1226178) baseStart_1226178 baseEnd_1226178 := by
    simpa [prefixWord, tailWord_1226178, baseEnd_1226178] using wordTrace_append hprefix tailTrace_1226178
  have hstable : (prefixWord ++ tailWord_1226178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226178).length < 2 ^ (prefixWord ++ tailWord_1226178).sum := by decide
  have hdescent : baseEnd_1226178 < baseStart_1226178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226200 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 8]
def baseStart_1226200 : Nat := 118140960795 + 1226200 * 2 ^ 59
def prefixEnd_1226200 : Nat := 4983230072969 + 3 ^ 40 * 1226200 * 2
def baseEnd_1226200 : Nat := 139917773009601715680181

theorem tailTrace_1226200 : CollatzResearch.WordTrace tailWord_1226200 prefixEnd_1226200 139917773009601715680181 := by
  unfold tailWord_1226200
  simp only [CollatzResearch.WordTrace]
  refine ⟨22361594078847146566234027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29815458771796195421645369 22361594078847146566234027)
  ·
    refine ⟨33542391118270719849351041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22361594078847146566234027 33542391118270719849351041)
    ·
      refine ⟨25156793338703039887013281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33542391118270719849351041 25156793338703039887013281)
      ·
        refine ⟨18867595004027279915259961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25156793338703039887013281 18867595004027279915259961)
        ·
          refine ⟨14150696253020459936444971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18867595004027279915259961 14150696253020459936444971)
          ·
            refine ⟨21226044379530689904667457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14150696253020459936444971 21226044379530689904667457)
            ·
              refine ⟨15919533284648017428500593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21226044379530689904667457 15919533284648017428500593)
              ·
                refine ⟨11939649963486013071375445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15919533284648017428500593 11939649963486013071375445)
                ·
                  refine ⟨139917773009601715680181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11939649963486013071375445 139917773009601715680181)
                  ·
                    rfl

theorem cell22_1226200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_1226200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226200 prefixEnd_1226200 := by exact prefixLift 1226200
  have htrace : WordTrace (prefixWord ++ tailWord_1226200) baseStart_1226200 baseEnd_1226200 := by
    simpa [prefixWord, tailWord_1226200, baseEnd_1226200] using wordTrace_append hprefix tailTrace_1226200
  have hstable : (prefixWord ++ tailWord_1226200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226200).length < 2 ^ (prefixWord ++ tailWord_1226200).sum := by decide
  have hdescent : baseEnd_1226200 < baseStart_1226200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226341 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 5]
def baseStart_1226341 : Nat := 118140960795 + 1226341 * 2 ^ 59
def prefixEnd_1226341 : Nat := 4983230072969 + 3 ^ 40 * 1226341 * 2
def baseEnd_1226341 : Nat := 139933862070109259755037

theorem tailTrace_1226341 : CollatzResearch.WordTrace tailWord_1226341 prefixEnd_1226341 139933862070109259755037 := by
  unfold tailWord_1226341
  simp only [CollatzResearch.WordTrace]
  refine ⟨44728330850183474213350877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29818887233455649475567251 44728330850183474213350877)
  ·
    refine ⟨16773124068818802830006579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44728330850183474213350877 16773124068818802830006579)
    ·
      refine ⟨25159686103228204245009869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16773124068818802830006579 25159686103228204245009869)
      ·
        refine ⟨9434882288710576591878701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25159686103228204245009869 9434882288710576591878701)
        ·
          refine ⟨3538080858266466221954513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9434882288710576591878701 3538080858266466221954513)
          ·
            refine ⟨2653560643699849666465885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3538080858266466221954513 2653560643699849666465885)
            ·
              refine ⟨995085241387443624924707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2653560643699849666465885 995085241387443624924707)
              ·
                refine ⟨1492627862081165437387061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995085241387443624924707 1492627862081165437387061)
                ·
                  refine ⟨139933862070109259755037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1492627862081165437387061 139933862070109259755037)
                  ·
                    rfl

theorem cell22_1226341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_1226341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226341 prefixEnd_1226341 := by exact prefixLift 1226341
  have htrace : WordTrace (prefixWord ++ tailWord_1226341) baseStart_1226341 baseEnd_1226341 := by
    simpa [prefixWord, tailWord_1226341, baseEnd_1226341] using wordTrace_append hprefix tailTrace_1226341
  have hstable : (prefixWord ++ tailWord_1226341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226341).length < 2 ^ (prefixWord ++ tailWord_1226341).sum := by decide
  have hdescent : baseEnd_1226341 < baseStart_1226341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226427 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 4, 6]
def baseStart_1226427 : Nat := 118140960795 + 1226427 * 2 ^ 59
def prefixEnd_1226427 : Nat := 4983230072969 + 3 ^ 40 * 1226427 * 2
def baseEnd_1226427 : Nat := 419831025767852221614847

theorem tailTrace_1226427 : CollatzResearch.WordTrace tailWord_1226427 prefixEnd_1226427 419831025767852221614847 := by
  unfold tailWord_1226427
  simp only [CollatzResearch.WordTrace]
  refine ⟨44731467527871910900981535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29820978351914607267321023 44731467527871910900981535)
  ·
    refine ⟨67097201291807866351472303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44731467527871910900981535 67097201291807866351472303)
    ·
      refine ⟨100645801937711799527208455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67097201291807866351472303 100645801937711799527208455)
      ·
        refine ⟨150968702906567699290812683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100645801937711799527208455 150968702906567699290812683)
        ·
          refine ⟨226453054359851548936219025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150968702906567699290812683 226453054359851548936219025)
          ·
            refine ⟨169839790769888661702164269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226453054359851548936219025 169839790769888661702164269)
            ·
              refine ⟨63689921538708248138311601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169839790769888661702164269 63689921538708248138311601)
              ·
                refine ⟨47767441154031186103733701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63689921538708248138311601 47767441154031186103733701)
                ·
                  refine ⟨8956395216380847394450069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47767441154031186103733701 8956395216380847394450069)
                  ·
                    refine ⟨419831025767852221614847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8956395216380847394450069 419831025767852221614847)
                    ·
                      rfl

theorem cell22_1226427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_1226427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226427 prefixEnd_1226427 := by exact prefixLift 1226427
  have htrace : WordTrace (prefixWord ++ tailWord_1226427) baseStart_1226427 baseEnd_1226427 := by
    simpa [prefixWord, tailWord_1226427, baseEnd_1226427] using wordTrace_append hprefix tailTrace_1226427
  have hstable : (prefixWord ++ tailWord_1226427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226427).length < 2 ^ (prefixWord ++ tailWord_1226427).sum := by decide
  have hdescent : baseEnd_1226427 < baseStart_1226427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226446 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_1226446 : Nat := 118140960795 + 1226446 * 2 ^ 59
def prefixEnd_1226446 : Nat := 4983230072969 + 3 ^ 40 * 1226446 * 2
def baseEnd_1226446 : Nat := 419837529856142505389789

theorem tailTrace_1226446 : CollatzResearch.WordTrace tailWord_1226446 prefixEnd_1226446 419837529856142505389789 := by
  unfold tailWord_1226446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591520064350384643240399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29821440343202051430615461 5591520064350384643240399)
  ·
    refine ⟨8387280096525576964860599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5591520064350384643240399 8387280096525576964860599)
    ·
      refine ⟨12580920144788365447290899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8387280096525576964860599 12580920144788365447290899)
      ·
        refine ⟨18871380217182548170936349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12580920144788365447290899 18871380217182548170936349)
        ·
          refine ⟨7076767581443455564101131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18871380217182548170936349 7076767581443455564101131)
          ·
            refine ⟨10615151372165183346151697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7076767581443455564101131 10615151372165183346151697)
            ·
              refine ⟨7961363529123887509613773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10615151372165183346151697 7961363529123887509613773)
              ·
                refine ⟨2985511323421457816105165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7961363529123887509613773 2985511323421457816105165)
                ·
                  refine ⟨1119566746283046681039437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2985511323421457816105165 1119566746283046681039437)
                  ·
                    refine ⟨419837529856142505389789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1119566746283046681039437 419837529856142505389789)
                    ·
                      rfl

theorem cell22_1226446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_1226446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226446 prefixEnd_1226446 := by exact prefixLift 1226446
  have htrace : WordTrace (prefixWord ++ tailWord_1226446) baseStart_1226446 baseEnd_1226446 := by
    simpa [prefixWord, tailWord_1226446, baseEnd_1226446] using wordTrace_append hprefix tailTrace_1226446
  have hstable : (prefixWord ++ tailWord_1226446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226446).length < 2 ^ (prefixWord ++ tailWord_1226446).sum := by decide
  have hdescent : baseEnd_1226446 < baseStart_1226446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226641 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_1226641 : Nat := 118140960795 + 1226641 * 2 ^ 59
def prefixEnd_1226641 : Nat := 4983230072969 + 3 ^ 40 * 1226641 * 2
def baseEnd_1226641 : Nat := 419904282341226996764191

theorem tailTrace_1226641 : CollatzResearch.WordTrace tailWord_1226641 prefixEnd_1226641 419904282341226996764191 := by
  unfold tailWord_1226641
  simp only [CollatzResearch.WordTrace]
  refine ⟨44739272749096625449271777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29826181832731083632847851 44739272749096625449271777)
  ·
    refine ⟨33554454561822469086953833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44739272749096625449271777 33554454561822469086953833)
    ·
      refine ⟨25165840921366851815215375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33554454561822469086953833 25165840921366851815215375)
      ·
        refine ⟨37748761382050277722823063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25165840921366851815215375 37748761382050277722823063)
        ·
          refine ⟨56623142073075416584234595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37748761382050277722823063 56623142073075416584234595)
          ·
            refine ⟨84934713109613124876351893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56623142073075416584234595 84934713109613124876351893)
            ·
              refine ⟨3981314677013115228578995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84934713109613124876351893 3981314677013115228578995)
              ·
                refine ⟨5971972015519672842868493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981314677013115228578995 5971972015519672842868493)
                ·
                  refine ⟨2239489505819877316075685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5971972015519672842868493 2239489505819877316075685)
                  ·
                    refine ⟨419904282341226996764191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2239489505819877316075685 419904282341226996764191)
                    ·
                      rfl

theorem cell22_1226641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_1226641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226641 prefixEnd_1226641 := by exact prefixLift 1226641
  have htrace : WordTrace (prefixWord ++ tailWord_1226641) baseStart_1226641 baseEnd_1226641 := by
    simpa [prefixWord, tailWord_1226641, baseEnd_1226641] using wordTrace_append hprefix tailTrace_1226641
  have hstable : (prefixWord ++ tailWord_1226641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226641).length < 2 ^ (prefixWord ++ tailWord_1226641).sum := by decide
  have hdescent : baseEnd_1226641 < baseStart_1226641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226673 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 6]
def baseStart_1226673 : Nat := 118140960795 + 1226673 * 2 ^ 59
def prefixEnd_1226673 : Nat := 4983230072969 + 3 ^ 40 * 1226673 * 2
def baseEnd_1226673 : Nat := 139971745531729859988031

theorem tailTrace_1226673 : CollatzResearch.WordTrace tailWord_1226673 prefixEnd_1226673 139971745531729859988031 := by
  unfold tailWord_1226673
  simp only [CollatzResearch.WordTrace]
  refine ⟨44740439884980694914436673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29826959923320463276291115 44740439884980694914436673)
  ·
    refine ⟨33555329913735521185827505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44740439884980694914436673 33555329913735521185827505)
    ·
      refine ⟨25166497435301640889370629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33555329913735521185827505 25166497435301640889370629)
      ·
        refine ⟨4718718269119057666756993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25166497435301640889370629 4718718269119057666756993)
        ·
          refine ⟨3539038701839293250067745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4718718269119057666756993 3539038701839293250067745)
          ·
            refine ⟨2654279026379469937550809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3539038701839293250067745 2654279026379469937550809)
            ·
              refine ⟨1990709269784602453163107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2654279026379469937550809 1990709269784602453163107)
              ·
                refine ⟨2986063904676903679744661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990709269784602453163107 2986063904676903679744661)
                ·
                  refine ⟨139971745531729859988031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2986063904676903679744661 139971745531729859988031)
                  ·
                    rfl

theorem cell22_1226673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_1226673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226673 prefixEnd_1226673 := by exact prefixLift 1226673
  have htrace : WordTrace (prefixWord ++ tailWord_1226673) baseStart_1226673 baseEnd_1226673 := by
    simpa [prefixWord, tailWord_1226673, baseEnd_1226673] using wordTrace_append hprefix tailTrace_1226673
  have hstable : (prefixWord ++ tailWord_1226673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226673).length < 2 ^ (prefixWord ++ tailWord_1226673).sum := by decide
  have hdescent : baseEnd_1226673 < baseStart_1226673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226761 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_1226761 : Nat := 118140960795 + 1226761 * 2 ^ 59
def prefixEnd_1226761 : Nat := 4983230072969 + 3 ^ 40 * 1226761 * 2
def baseEnd_1226761 : Nat := 419945360793586683763823

theorem tailTrace_1226761 : CollatzResearch.WordTrace tailWord_1226761 prefixEnd_1226761 419945360793586683763823 := by
  unfold tailWord_1226761
  simp only [CollatzResearch.WordTrace]
  refine ⟨44743649508661885943640137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29829099672441257295760091 44743649508661885943640137)
  ·
    refine ⟨33557737131496414457730103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44743649508661885943640137 33557737131496414457730103)
    ·
      refine ⟨50336605697244621686595155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33557737131496414457730103 50336605697244621686595155)
      ·
        refine ⟨75504908545866932529892733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50336605697244621686595155 75504908545866932529892733)
        ·
          refine ⟨28314340704700099698709775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75504908545866932529892733 28314340704700099698709775)
          ·
            refine ⟨42471511057050149548064663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28314340704700099698709775 42471511057050149548064663)
            ·
              refine ⟨63707266585575224322096995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42471511057050149548064663 63707266585575224322096995)
              ·
                refine ⟨95560899878362836483145493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63707266585575224322096995 95560899878362836483145493)
                ·
                  refine ⟨4479417181798257960147445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95560899878362836483145493 4479417181798257960147445)
                  ·
                    refine ⟨419945360793586683763823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4479417181798257960147445 419945360793586683763823)
                    ·
                      rfl

theorem cell22_1226761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_1226761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226761 prefixEnd_1226761 := by exact prefixLift 1226761
  have htrace : WordTrace (prefixWord ++ tailWord_1226761) baseStart_1226761 baseEnd_1226761 := by
    simpa [prefixWord, tailWord_1226761, baseEnd_1226761] using wordTrace_append hprefix tailTrace_1226761
  have hstable : (prefixWord ++ tailWord_1226761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226761).length < 2 ^ (prefixWord ++ tailWord_1226761).sum := by decide
  have hdescent : baseEnd_1226761 < baseStart_1226761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226780 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 5]
def baseStart_1226780 : Nat := 118140960795 + 1226780 * 2 ^ 59
def prefixEnd_1226780 : Nat := 4983230072969 + 3 ^ 40 * 1226780 * 2
def baseEnd_1226780 : Nat := 139983954960625655846255

theorem tailTrace_1226780 : CollatzResearch.WordTrace tailWord_1226780 prefixEnd_1226780 139983954960625655846255 := by
  unfold tailWord_1226780
  simp only [CollatzResearch.WordTrace]
  refine ⟨22372171247796526094290897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29829561663728701459054529 22372171247796526094290897)
  ·
    refine ⟨16779128435847394570718173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22372171247796526094290897 16779128435847394570718173)
    ·
      refine ⟨6292173163442772964019315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16779128435847394570718173 6292173163442772964019315)
      ·
        refine ⟨9438259745164159446028973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6292173163442772964019315 9438259745164159446028973)
        ·
          refine ⟨3539347404436559792260865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9438259745164159446028973 3539347404436559792260865)
          ·
            refine ⟨2654510553327419844195649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3539347404436559792260865 2654510553327419844195649)
            ·
              refine ⟨1990882914995564883146737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2654510553327419844195649 1990882914995564883146737)
              ·
                refine ⟨1493162186246673662360053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1990882914995564883146737 1493162186246673662360053)
                ·
                  refine ⟨139983954960625655846255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1493162186246673662360053 139983954960625655846255)
                  ·
                    rfl

theorem cell22_1226780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_1226780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226780 prefixEnd_1226780 := by exact prefixLift 1226780
  have htrace : WordTrace (prefixWord ++ tailWord_1226780) baseStart_1226780 baseEnd_1226780 := by
    simpa [prefixWord, tailWord_1226780, baseEnd_1226780] using wordTrace_append hprefix tailTrace_1226780
  have hstable : (prefixWord ++ tailWord_1226780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226780).length < 2 ^ (prefixWord ++ tailWord_1226780).sum := by decide
  have hdescent : baseEnd_1226780 < baseStart_1226780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226823 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 1, 5]
def baseStart_1226823 : Nat := 118140960795 + 1226823 * 2 ^ 59
def prefixEnd_1226823 : Nat := 4983230072969 + 3 ^ 40 * 1226823 * 2
def baseEnd_1226823 : Nat := 419966584660639188713633

theorem tailTrace_1226823 : CollatzResearch.WordTrace tailWord_1226823 prefixEnd_1226823 419966584660639188713633 := by
  unfold tailWord_1226823
  simp only [CollatzResearch.WordTrace]
  refine ⟨44745910834437270532397123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29830607222958180354931415 44745910834437270532397123)
  ·
    refine ⟨67118866251655905798595685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44745910834437270532397123 67118866251655905798595685)
    ·
      refine ⟨12584787422185482337236691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67118866251655905798595685 12584787422185482337236691)
      ·
        refine ⟨18877181133278223505855037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12584787422185482337236691 18877181133278223505855037)
        ·
          refine ⟨7078942924979333814695639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18877181133278223505855037 7078942924979333814695639)
          ·
            refine ⟨10618414387469000722043459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7078942924979333814695639 10618414387469000722043459)
            ·
              refine ⟨15927621581203501083065189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10618414387469000722043459 15927621581203501083065189)
              ·
                refine ⟨2986429046475656453074723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15927621581203501083065189 2986429046475656453074723)
                ·
                  refine ⟨4479643569713484679612085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986429046475656453074723 4479643569713484679612085)
                  ·
                    refine ⟨419966584660639188713633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4479643569713484679612085 419966584660639188713633)
                    ·
                      rfl

theorem cell22_1226823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_1226823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226823 prefixEnd_1226823 := by exact prefixLift 1226823
  have htrace : WordTrace (prefixWord ++ tailWord_1226823) baseStart_1226823 baseEnd_1226823 := by
    simpa [prefixWord, tailWord_1226823, baseEnd_1226823] using wordTrace_append hprefix tailTrace_1226823
  have hstable : (prefixWord ++ tailWord_1226823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226823).length < 2 ^ (prefixWord ++ tailWord_1226823).sum := by decide
  have hdescent : baseEnd_1226823 < baseStart_1226823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226825 : List Nat := [1, 2, 1, 1, 2, 2, 6, 3, 4]
def baseStart_1226825 : Nat := 118140960795 + 1226825 * 2 ^ 59
def prefixEnd_1226825 : Nat := 4983230072969 + 3 ^ 40 * 1226825 * 2
def baseEnd_1226825 : Nat := 139989089767170616721209

theorem tailTrace_1226825 : CollatzResearch.WordTrace tailWord_1226825 prefixEnd_1226825 139989089767170616721209 := by
  unfold tailWord_1226825
  simp only [CollatzResearch.WordTrace]
  refine ⟨44745983780430024873969929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29830655853620016582646619 44745983780430024873969929)
  ·
    refine ⟨33559487835322518655477447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44745983780430024873969929 33559487835322518655477447)
    ·
      refine ⟨50339231752983777983216171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33559487835322518655477447 50339231752983777983216171)
      ·
        refine ⟨75508847629475666974824257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50339231752983777983216171 75508847629475666974824257)
        ·
          refine ⟨56631635722106750231118193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75508847629475666974824257 56631635722106750231118193)
          ·
            refine ⟨42473726791580062673338645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56631635722106750231118193 42473726791580062673338645)
            ·
              refine ⟨1990955943355315437812749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42473726791580062673338645 1990955943355315437812749)
              ·
                refine ⟨746608478758243289179781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1990955943355315437812749 746608478758243289179781)
                ·
                  refine ⟨139989089767170616721209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 746608478758243289179781 139989089767170616721209)
                  ·
                    rfl

theorem cell22_1226825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 4].length) (baseStart_1226825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226825 prefixEnd_1226825 := by exact prefixLift 1226825
  have htrace : WordTrace (prefixWord ++ tailWord_1226825) baseStart_1226825 baseEnd_1226825 := by
    simpa [prefixWord, tailWord_1226825, baseEnd_1226825] using wordTrace_append hprefix tailTrace_1226825
  have hstable : (prefixWord ++ tailWord_1226825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226825).length < 2 ^ (prefixWord ++ tailWord_1226825).sum := by decide
  have hdescent : baseEnd_1226825 < baseStart_1226825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226840 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 4, 3]
def baseStart_1226840 : Nat := 118140960795 + 1226840 * 2 ^ 59
def prefixEnd_1226840 : Nat := 4983230072969 + 3 ^ 40 * 1226840 * 2
def baseEnd_1226840 : Nat := 419972404108056811038581

theorem tailTrace_1226840 : CollatzResearch.WordTrace tailWord_1226840 prefixEnd_1226840 419972404108056811038581 := by
  unfold tailWord_1226840
  simp only [CollatzResearch.WordTrace]
  refine ⟨22373265437687841217882987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29831020583583788290510649 22373265437687841217882987)
  ·
    refine ⟨33559898156531761826824481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22373265437687841217882987 33559898156531761826824481)
    ·
      refine ⟨25169923617398821370118361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33559898156531761826824481 25169923617398821370118361)
      ·
        refine ⟨18877442713049116027588771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25169923617398821370118361 18877442713049116027588771)
        ·
          refine ⟨28316164069573674041383157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18877442713049116027588771 28316164069573674041383157)
          ·
            refine ⟨2654640381522531941379671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28316164069573674041383157 2654640381522531941379671)
            ·
              refine ⟨3981960572283797912069507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654640381522531941379671 3981960572283797912069507)
              ·
                refine ⟨5972940858425696868104261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981960572283797912069507 5972940858425696868104261)
                ·
                  refine ⟨1119926410954818162769549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5972940858425696868104261 1119926410954818162769549)
                  ·
                    refine ⟨419972404108056811038581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1119926410954818162769549 419972404108056811038581)
                    ·
                      rfl

theorem cell22_1226840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_1226840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226840 prefixEnd_1226840 := by exact prefixLift 1226840
  have htrace : WordTrace (prefixWord ++ tailWord_1226840) baseStart_1226840 baseEnd_1226840 := by
    simpa [prefixWord, tailWord_1226840, baseEnd_1226840] using wordTrace_append hprefix tailTrace_1226840
  have hstable : (prefixWord ++ tailWord_1226840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226840).length < 2 ^ (prefixWord ++ tailWord_1226840).sum := by decide
  have hdescent : baseEnd_1226840 < baseStart_1226840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226857 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 2, 3]
def baseStart_1226857 : Nat := 118140960795 + 1226857 * 2 ^ 59
def prefixEnd_1226857 : Nat := 4983230072969 + 3 ^ 40 * 1226857 * 2
def baseEnd_1226857 : Nat := 419978223555474433363529

theorem tailTrace_1226857 : CollatzResearch.WordTrace tailWord_1226857 prefixEnd_1226857 419978223555474433363529 := by
  unfold tailWord_1226857
  simp only [CollatzResearch.WordTrace]
  refine ⟨44747150916314094339134825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29831433944209396226089883 44747150916314094339134825)
  ·
    refine ⟨33560363187235570754351119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44747150916314094339134825 33560363187235570754351119)
    ·
      refine ⟨50340544780853356131526679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33560363187235570754351119 50340544780853356131526679)
      ·
        refine ⟨75510817171280034197290019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50340544780853356131526679 75510817171280034197290019)
        ·
          refine ⟨113266225756920051295935029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75510817171280034197290019 113266225756920051295935029)
          ·
            refine ⟨10618708664711254808993909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113266225756920051295935029 10618708664711254808993909)
            ·
              refine ⟨995503937316680138343179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10618708664711254808993909 995503937316680138343179)
              ·
                refine ⟨1493255905975020207514769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995503937316680138343179 1493255905975020207514769)
                ·
                  refine ⟨1119941929481265155636077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1493255905975020207514769 1119941929481265155636077)
                  ·
                    refine ⟨419978223555474433363529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1119941929481265155636077 419978223555474433363529)
                    ·
                      rfl

theorem cell22_1226857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 3].length) (baseStart_1226857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226857 prefixEnd_1226857 := by exact prefixLift 1226857
  have htrace : WordTrace (prefixWord ++ tailWord_1226857) baseStart_1226857 baseEnd_1226857 := by
    simpa [prefixWord, tailWord_1226857, baseEnd_1226857] using wordTrace_append hprefix tailTrace_1226857
  have hstable : (prefixWord ++ tailWord_1226857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226857).length < 2 ^ (prefixWord ++ tailWord_1226857).sum := by decide
  have hdescent : baseEnd_1226857 < baseStart_1226857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226870 : List Nat := [5, 1, 1, 2, 1, 3, 1, 8]
def baseStart_1226870 : Nat := 118140960795 + 1226870 * 2 ^ 59
def prefixEnd_1226870 : Nat := 4983230072969 + 3 ^ 40 * 1226870 * 2
def baseEnd_1226870 : Nat := 46664741524571859198721

theorem tailTrace_1226870 : CollatzResearch.WordTrace tailWord_1226870 prefixEnd_1226870 46664741524571859198721 := by
  unfold tailWord_1226870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796726566579187347459879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29831750043511331706238709 2796726566579187347459879)
  ·
    refine ⟨4195089849868781021189819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2796726566579187347459879 4195089849868781021189819)
    ·
      refine ⟨6292634774803171531784729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4195089849868781021189819 6292634774803171531784729)
      ·
        refine ⟨4719476081102378648838547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6292634774803171531784729 4719476081102378648838547)
        ·
          refine ⟨7079214121653567973257821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4719476081102378648838547 7079214121653567973257821)
          ·
            refine ⟨2654705295620087989971683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7079214121653567973257821 2654705295620087989971683)
            ·
              refine ⟨3982057943430131984957525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654705295620087989971683 3982057943430131984957525)
              ·
                refine ⟨46664741524571859198721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3982057943430131984957525 46664741524571859198721)
                ·
                  rfl

theorem cell22_1226870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_1226870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226870 prefixEnd_1226870 := by exact prefixLift 1226870
  have htrace : WordTrace (prefixWord ++ tailWord_1226870) baseStart_1226870 baseEnd_1226870 := by
    simpa [prefixWord, tailWord_1226870, baseEnd_1226870] using wordTrace_append hprefix tailTrace_1226870
  have hstable : (prefixWord ++ tailWord_1226870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226870).length < 2 ^ (prefixWord ++ tailWord_1226870).sum := by decide
  have hdescent : baseEnd_1226870 < baseStart_1226870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226975 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 6, 3]
def baseStart_1226975 : Nat := 118140960795 + 1226975 * 2 ^ 59
def prefixEnd_1226975 : Nat := 4983230072969 + 3 ^ 40 * 1226975 * 2
def baseEnd_1226975 : Nat := 420018617366961458913167

theorem tailTrace_1226975 : CollatzResearch.WordTrace tailWord_1226975 prefixEnd_1226975 420018617366961458913167 := by
  unfold tailWord_1226975
  simp only [CollatzResearch.WordTrace]
  refine ⟨44751454729886600491930379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29834303153257733661286919 44751454729886600491930379)
  ·
    refine ⟨67127182094829900737895569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44751454729886600491930379 67127182094829900737895569)
    ·
      refine ⟨50345386571122425553421677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67127182094829900737895569 50345386571122425553421677)
      ·
        refine ⟨18879519964170909582533129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50345386571122425553421677 18879519964170909582533129)
        ·
          refine ⟨14159639973128182186899847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18879519964170909582533129 14159639973128182186899847)
          ·
            refine ⟨21239459959692273280349771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14159639973128182186899847 21239459959692273280349771)
            ·
              refine ⟨31859189939538409920524657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21239459959692273280349771 31859189939538409920524657)
              ·
                refine ⟨23894392454653807440393493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31859189939538409920524657 23894392454653807440393493)
                ·
                  refine ⟨1120049646311897223768445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23894392454653807440393493 1120049646311897223768445)
                  ·
                    refine ⟨420018617366961458913167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1120049646311897223768445 420018617366961458913167)
                    ·
                      rfl

theorem cell22_1226975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_1226975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226975 prefixEnd_1226975 := by exact prefixLift 1226975
  have htrace : WordTrace (prefixWord ++ tailWord_1226975) baseStart_1226975 baseEnd_1226975 := by
    simpa [prefixWord, tailWord_1226975, baseEnd_1226975] using wordTrace_append hprefix tailTrace_1226975
  have hstable : (prefixWord ++ tailWord_1226975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226975).length < 2 ^ (prefixWord ++ tailWord_1226975).sum := by decide
  have hdescent : baseEnd_1226975 < baseStart_1226975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226994 : List Nat := [3, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_1226994 : Nat := 118140960795 + 1226994 * 2 ^ 59
def prefixEnd_1226994 : Nat := 4983230072969 + 3 ^ 40 * 1226994 * 2
def baseEnd_1226994 : Nat := 140008373818417247562703

theorem tailTrace_1226994 : CollatzResearch.WordTrace tailWord_1226994 prefixEnd_1226994 140008373818417247562703 := by
  unfold tailWord_1226994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188036929204441684218009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29834765144545177824581357 11188036929204441684218009)
  ·
    refine ⟨8391027696903331263163507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11188036929204441684218009 8391027696903331263163507)
    ·
      refine ⟨12586541545354996894745261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8391027696903331263163507 12586541545354996894745261)
      ·
        refine ⟨4719953079508123835529473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12586541545354996894745261 4719953079508123835529473)
        ·
          refine ⟨3539964809631092876647105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4719953079508123835529473 3539964809631092876647105)
          ·
            refine ⟨2654973607223319657485329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3539964809631092876647105 2654973607223319657485329)
            ·
              refine ⟨1991230205417489743113997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2654973607223319657485329 1991230205417489743113997)
              ·
                refine ⟨746711327031558653667749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1991230205417489743113997 746711327031558653667749)
                ·
                  refine ⟨140008373818417247562703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 746711327031558653667749 140008373818417247562703)
                  ·
                    rfl

theorem cell22_1226994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_1226994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226994 prefixEnd_1226994 := by exact prefixLift 1226994
  have htrace : WordTrace (prefixWord ++ tailWord_1226994) baseStart_1226994 baseEnd_1226994 := by
    simpa [prefixWord, tailWord_1226994, baseEnd_1226994] using wordTrace_append hprefix tailTrace_1226994
  have hstable : (prefixWord ++ tailWord_1226994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226994).length < 2 ^ (prefixWord ++ tailWord_1226994).sum := by decide
  have hdescent : baseEnd_1226994 < baseStart_1226994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227003 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 3, 9]
def baseStart_1227003 : Nat := 118140960795 + 1227003 * 2 ^ 59
def prefixEnd_1227003 : Nat := 4983230072969 + 3 ^ 40 * 1227003 * 2
def baseEnd_1227003 : Nat := 420028202339178719213081

theorem tailTrace_1227003 : CollatzResearch.WordTrace tailWord_1227003 prefixEnd_1227003 420028202339178719213081 := by
  unfold tailWord_1227003
  simp only [CollatzResearch.WordTrace]
  refine ⟨44752475973785161273949663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29834983982523440849299775 44752475973785161273949663)
  ·
    refine ⟨67128713960677741910924495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44752475973785161273949663 67128713960677741910924495)
    ·
      refine ⟨100693070941016612866386743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67128713960677741910924495 100693070941016612866386743)
      ·
        refine ⟨151039606411524919299580115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100693070941016612866386743 151039606411524919299580115)
        ·
          refine ⟨226559409617287378949370173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151039606411524919299580115 226559409617287378949370173)
          ·
            refine ⟨84959778606482767106013815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226559409617287378949370173 84959778606482767106013815)
            ·
              refine ⟨127439667909724150659020723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84959778606482767106013815 127439667909724150659020723)
              ·
                refine ⟨191159501864586225988531085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127439667909724150659020723 191159501864586225988531085)
                ·
                  refine ⟨71684813199219834745699157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191159501864586225988531085 71684813199219834745699157)
                  ·
                    refine ⟨420028202339178719213081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 71684813199219834745699157 420028202339178719213081)
                    ·
                      rfl

theorem cell22_1227003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_1227003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227003 prefixEnd_1227003 := by exact prefixLift 1227003
  have htrace : WordTrace (prefixWord ++ tailWord_1227003) baseStart_1227003 baseEnd_1227003 := by
    simpa [prefixWord, tailWord_1227003, baseEnd_1227003] using wordTrace_append hprefix tailTrace_1227003
  have hstable : (prefixWord ++ tailWord_1227003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227003).length < 2 ^ (prefixWord ++ tailWord_1227003).sum := by decide
  have hdescent : baseEnd_1227003 < baseStart_1227003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227071 : List Nat := [1, 1, 2, 2, 4, 1, 5, 2, 1, 3]
def baseStart_1227071 : Nat := 118140960795 + 1227071 * 2 ^ 59
def prefixEnd_1227071 : Nat := 4983230072969 + 3 ^ 40 * 1227071 * 2
def baseEnd_1227071 : Nat := 420051480128849208512873

theorem tailTrace_1227071 : CollatzResearch.WordTrace tailWord_1227071 prefixEnd_1227071 420051480128849208512873 := by
  unfold tailWord_1227071
  simp only [CollatzResearch.WordTrace]
  refine ⟨44754956137538808887425067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29836637425025872591616711 44754956137538808887425067)
  ·
    refine ⟨67132434206308213331137601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44754956137538808887425067 67132434206308213331137601)
    ·
      refine ⟨50349325654731159998353201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67132434206308213331137601 50349325654731159998353201)
      ·
        refine ⟨37761994241048369998764901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50349325654731159998353201 37761994241048369998764901)
        ·
          refine ⟨7080373920196569374768419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37761994241048369998764901 7080373920196569374768419)
          ·
            refine ⟨10620560880294854062152629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080373920196569374768419 10620560880294854062152629)
            ·
              refine ⟨995677582527642568326809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10620560880294854062152629 995677582527642568326809)
              ·
                refine ⟨746758186895731926245107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995677582527642568326809 746758186895731926245107)
                ·
                  refine ⟨1120137280343597889367661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746758186895731926245107 1120137280343597889367661)
                  ·
                    refine ⟨420051480128849208512873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1120137280343597889367661 420051480128849208512873)
                    ·
                      rfl

theorem cell22_1227071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 3].length) (baseStart_1227071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227071 prefixEnd_1227071 := by exact prefixLift 1227071
  have htrace : WordTrace (prefixWord ++ tailWord_1227071) baseStart_1227071 baseEnd_1227071 := by
    simpa [prefixWord, tailWord_1227071, baseEnd_1227071] using wordTrace_append hprefix tailTrace_1227071
  have hstable : (prefixWord ++ tailWord_1227071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227071).length < 2 ^ (prefixWord ++ tailWord_1227071).sum := by decide
  have hdescent : baseEnd_1227071 < baseStart_1227071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227095 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 8]
def baseStart_1227095 : Nat := 118140960795 + 1227095 * 2 ^ 59
def prefixEnd_1227095 : Nat := 4983230072969 + 3 ^ 40 * 1227095 * 2
def baseEnd_1227095 : Nat := 140019898606440381970933

theorem tailTrace_1227095 : CollatzResearch.WordTrace tailWord_1227095 prefixEnd_1227095 140019898606440381970933 := by
  unfold tailWord_1227095
  simp only [CollatzResearch.WordTrace]
  refine ⟨44755831489451860986298739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29837220992967907324199159 44755831489451860986298739)
  ·
    refine ⟨67133747234177791479448109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44755831489451860986298739 67133747234177791479448109)
    ·
      refine ⟨25175155212816671804793041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67133747234177791479448109 25175155212816671804793041)
      ·
        refine ⟨18881366409612503853594781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25175155212816671804793041 18881366409612503853594781)
        ·
          refine ⟨7080512403604688945098043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18881366409612503853594781 7080512403604688945098043)
          ·
            refine ⟨10620768605407033417647065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080512403604688945098043 10620768605407033417647065)
            ·
              refine ⟨7965576454055275063235299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10620768605407033417647065 7965576454055275063235299)
              ·
                refine ⟨11948364681082912594852949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7965576454055275063235299 11948364681082912594852949)
                ·
                  refine ⟨140019898606440381970933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11948364681082912594852949 140019898606440381970933)
                  ·
                    rfl

theorem cell22_1227095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 8].length) (baseStart_1227095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227095 prefixEnd_1227095 := by exact prefixLift 1227095
  have htrace : WordTrace (prefixWord ++ tailWord_1227095) baseStart_1227095 baseEnd_1227095 := by
    simpa [prefixWord, tailWord_1227095, baseEnd_1227095] using wordTrace_append hprefix tailTrace_1227095
  have hstable : (prefixWord ++ tailWord_1227095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227095).length < 2 ^ (prefixWord ++ tailWord_1227095).sum := by decide
  have hdescent : baseEnd_1227095 < baseStart_1227095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227144 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 2, 3]
def baseStart_1227144 : Nat := 118140960795 + 1227144 * 2 ^ 59
def prefixEnd_1227144 : Nat := 4983230072969 + 3 ^ 40 * 1227144 * 2
def baseEnd_1227144 : Nat := 420076469520701351437649

theorem tailTrace_1227144 : CollatzResearch.WordTrace tailWord_1227144 prefixEnd_1227144 420076469520701351437649 := by
  unfold tailWord_1227144
  simp only [CollatzResearch.WordTrace]
  refine ⟨22378809333137171177416243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29838412444182894903221657 22378809333137171177416243)
  ·
    refine ⟨33568213999705756766124365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22378809333137171177416243 33568213999705756766124365)
    ·
      refine ⟨12588080249889658787296637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33568213999705756766124365 12588080249889658787296637)
      ·
        refine ⟨4720530093708622045236239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12588080249889658787296637 4720530093708622045236239)
        ·
          refine ⟨7080795140562933067854359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4720530093708622045236239 7080795140562933067854359)
          ·
            refine ⟨10621192710844399601781539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080795140562933067854359 10621192710844399601781539)
            ·
              refine ⟨15931789066266599402672309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10621192710844399601781539 15931789066266599402672309)
              ·
                refine ⟨1493605224962493694000529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15931789066266599402672309 1493605224962493694000529)
                ·
                  refine ⟨1120203918721870270500397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1493605224962493694000529 1120203918721870270500397)
                  ·
                    refine ⟨420076469520701351437649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1120203918721870270500397 420076469520701351437649)
                    ·
                      rfl

theorem cell22_1227144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_1227144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227144 prefixEnd_1227144 := by exact prefixLift 1227144
  have htrace : WordTrace (prefixWord ++ tailWord_1227144) baseStart_1227144 baseEnd_1227144 := by
    simpa [prefixWord, tailWord_1227144, baseEnd_1227144] using wordTrace_append hprefix tailTrace_1227144
  have hstable : (prefixWord ++ tailWord_1227144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227144).length < 2 ^ (prefixWord ++ tailWord_1227144).sum := by decide
  have hdescent : baseEnd_1227144 < baseStart_1227144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227292 : List Nat := [2, 2, 3, 1, 2, 12]
def baseStart_1227292 : Nat := 118140960795 + 1227292 * 2 ^ 59
def prefixEnd_1227292 : Nat := 4983230072969 + 3 ^ 40 * 1227292 * 2
def baseEnd_1227292 : Nat := 5186754727719485169595

theorem tailTrace_1227292 : CollatzResearch.WordTrace tailWord_1227292 prefixEnd_1227292 5186754727719485169595 := by
  unfold tailWord_1227292
  simp only [CollatzResearch.WordTrace]
  refine ⟨22381508334869081815610065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29842011113158775754146753 22381508334869081815610065)
  ·
    refine ⟨16786131251151811361707549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22381508334869081815610065 16786131251151811361707549)
    ·
      refine ⟨6294799219181929260640331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16786131251151811361707549 6294799219181929260640331)
      ·
        refine ⟨9442198828772893890960497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6294799219181929260640331 9442198828772893890960497)
        ·
          refine ⟨7081649121579670418220373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9442198828772893890960497 7081649121579670418220373)
          ·
            refine ⟨5186754727719485169595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7081649121579670418220373 5186754727719485169595)
            ·
              rfl

theorem cell22_1227292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 12].length) (baseStart_1227292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227292 prefixEnd_1227292 := by exact prefixLift 1227292
  have htrace : WordTrace (prefixWord ++ tailWord_1227292) baseStart_1227292 baseEnd_1227292 := by
    simpa [prefixWord, tailWord_1227292, baseEnd_1227292] using wordTrace_append hprefix tailTrace_1227292
  have hstable : (prefixWord ++ tailWord_1227292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227292).length < 2 ^ (prefixWord ++ tailWord_1227292).sum := by decide
  have hdescent : baseEnd_1227292 < baseStart_1227292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227332 : List Nat := [2, 3, 5, 1, 1, 1, 2, 3, 4]
def baseStart_1227332 : Nat := 118140960795 + 1227332 * 2 ^ 59
def prefixEnd_1227332 : Nat := 4983230072969 + 3 ^ 40 * 1227332 * 2
def baseEnd_1227332 : Nat := 140046941920910509245691

theorem tailTrace_1227332 : CollatzResearch.WordTrace tailWord_1227332 prefixEnd_1227332 140046941920910509245691 := by
  unfold tailWord_1227332
  simp only [CollatzResearch.WordTrace]
  refine ⟨22382237794796625231338125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29842983726395500308450833 22382237794796625231338125)
  ·
    refine ⟨8393339173048734461751797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22382237794796625231338125 8393339173048734461751797)
    ·
      refine ⟨786875547473318855789231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8393339173048734461751797 786875547473318855789231)
      ·
        refine ⟨1180313321209978283683847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786875547473318855789231 1180313321209978283683847)
        ·
          refine ⟨1770469981814967425525771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180313321209978283683847 1770469981814967425525771)
          ·
            refine ⟨2655704972722451138288657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770469981814967425525771 2655704972722451138288657)
            ·
              refine ⟨1991778729541838353716493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2655704972722451138288657 1991778729541838353716493)
              ·
                refine ⟨746917023578189382643685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1991778729541838353716493 746917023578189382643685)
                ·
                  refine ⟨140046941920910509245691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 746917023578189382643685 140046941920910509245691)
                  ·
                    rfl

theorem cell22_1227332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_1227332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227332 prefixEnd_1227332 := by exact prefixLift 1227332
  have htrace : WordTrace (prefixWord ++ tailWord_1227332) baseStart_1227332 baseEnd_1227332 := by
    simpa [prefixWord, tailWord_1227332, baseEnd_1227332] using wordTrace_append hprefix tailTrace_1227332
  have hstable : (prefixWord ++ tailWord_1227332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227332).length < 2 ^ (prefixWord ++ tailWord_1227332).sum := by decide
  have hdescent : baseEnd_1227332 < baseStart_1227332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227429 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_1227429 : Nat := 118140960795 + 1227429 * 2 ^ 59
def prefixEnd_1227429 : Nat := 4983230072969 + 3 ^ 40 * 1227429 * 2
def baseEnd_1227429 : Nat := 420174030845055608061775

theorem tailTrace_1227429 : CollatzResearch.WordTrace tailWord_1227429 prefixEnd_1227429 420174030845055608061775 := by
  unfold tailWord_1227429
  simp only [CollatzResearch.WordTrace]
  refine ⟨44768013470241836028957341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29845342313494557352638227 44768013470241836028957341)
  ·
    refine ⟨16788005051340688510859003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44768013470241836028957341 16788005051340688510859003)
    ·
      refine ⟨25182007577011032766288505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16788005051340688510859003 25182007577011032766288505)
      ·
        refine ⟨18886505682758274574716379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25182007577011032766288505 18886505682758274574716379)
        ·
          refine ⟨28329758524137411862074569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18886505682758274574716379 28329758524137411862074569)
          ·
            refine ⟨21247318893103058896555927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28329758524137411862074569 21247318893103058896555927)
            ·
              refine ⟨31870978339654588344833891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21247318893103058896555927 31870978339654588344833891)
              ·
                refine ⟨47806467509481882517250837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31870978339654588344833891 47806467509481882517250837)
                ·
                  refine ⟨2240928164506963242996133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47806467509481882517250837 2240928164506963242996133)
                  ·
                    refine ⟨420174030845055608061775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2240928164506963242996133 420174030845055608061775)
                    ·
                      rfl

theorem cell22_1227429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_1227429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227429 prefixEnd_1227429 := by exact prefixLift 1227429
  have htrace : WordTrace (prefixWord ++ tailWord_1227429) baseStart_1227429 baseEnd_1227429 := by
    simpa [prefixWord, tailWord_1227429, baseEnd_1227429] using wordTrace_append hprefix tailTrace_1227429
  have hstable : (prefixWord ++ tailWord_1227429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227429).length < 2 ^ (prefixWord ++ tailWord_1227429).sum := by decide
  have hdescent : baseEnd_1227429 < baseStart_1227429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227493 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_1227493 : Nat := 118140960795 + 1227493 * 2 ^ 59
def prefixEnd_1227493 : Nat := 4983230072969 + 3 ^ 40 * 1227493 * 2
def baseEnd_1227493 : Nat := 420195939352980774461579

theorem tailTrace_1227493 : CollatzResearch.WordTrace tailWord_1227493 prefixEnd_1227493 420195939352980774461579 := by
  unfold tailWord_1227493
  simp only [CollatzResearch.WordTrace]
  refine ⟨44770347742009974959287133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29846898494673316639524755 44770347742009974959287133)
  ·
    refine ⟨16788880403253740609732675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44770347742009974959287133 16788880403253740609732675)
    ·
      refine ⟨25183320604880610914599013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16788880403253740609732675 25183320604880610914599013)
      ·
        refine ⟨4721872613415114546487315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25183320604880610914599013 4721872613415114546487315)
        ·
          refine ⟨7082808920122671819730973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721872613415114546487315 7082808920122671819730973)
          ·
            refine ⟨2656053345046001932399115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7082808920122671819730973 2656053345046001932399115)
            ·
              refine ⟨3984080017569002898598673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656053345046001932399115 3984080017569002898598673)
              ·
                refine ⟨2988060013176752173949005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3984080017569002898598673 2988060013176752173949005)
                ·
                  refine ⟨1120522504941282065230877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2988060013176752173949005 1120522504941282065230877)
                  ·
                    refine ⟨420195939352980774461579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1120522504941282065230877 420195939352980774461579)
                    ·
                      rfl

theorem cell22_1227493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_1227493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227493 prefixEnd_1227493 := by exact prefixLift 1227493
  have htrace : WordTrace (prefixWord ++ tailWord_1227493) baseStart_1227493 baseEnd_1227493 := by
    simpa [prefixWord, tailWord_1227493, baseEnd_1227493] using wordTrace_append hprefix tailTrace_1227493
  have hstable : (prefixWord ++ tailWord_1227493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227493).length < 2 ^ (prefixWord ++ tailWord_1227493).sum := by decide
  have hdescent : baseEnd_1227493 < baseStart_1227493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227504 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_1227504 : Nat := 118140960795 + 1227504 * 2 ^ 59
def prefixEnd_1227504 : Nat := 4983230072969 + 3 ^ 40 * 1227504 * 2
def baseEnd_1227504 : Nat := 420199704877780412436545

theorem tailTrace_1227504 : CollatzResearch.WordTrace tailWord_1227504 prefixEnd_1227504 420199704877780412436545 := by
  unfold tailWord_1227504
  simp only [CollatzResearch.WordTrace]
  refine ⟨22385374472485061918968783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29847165963313415891958377 22385374472485061918968783)
  ·
    refine ⟨33578061708727592878453175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22385374472485061918968783 33578061708727592878453175)
    ·
      refine ⟨50367092563091389317679763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33578061708727592878453175 50367092563091389317679763)
      ·
        refine ⟨75550638844637083976519645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50367092563091389317679763 75550638844637083976519645)
        ·
          refine ⟨28331489566738906491194867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75550638844637083976519645 28331489566738906491194867)
          ·
            refine ⟨42497234350108359736792301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28331489566738906491194867 42497234350108359736792301)
            ·
              refine ⟨15936462881290634901297113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42497234350108359736792301 15936462881290634901297113)
              ·
                refine ⟨11952347160967976175972835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15936462881290634901297113 11952347160967976175972835)
                ·
                  refine ⟨17928520741451964263959253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11952347160967976175972835 17928520741451964263959253)
                  ·
                    refine ⟨420199704877780412436545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17928520741451964263959253 420199704877780412436545)
                    ·
                      rfl

theorem cell22_1227504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_1227504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227504 prefixEnd_1227504 := by exact prefixLift 1227504
  have htrace : WordTrace (prefixWord ++ tailWord_1227504) baseStart_1227504 baseEnd_1227504 := by
    simpa [prefixWord, tailWord_1227504, baseEnd_1227504] using wordTrace_append hprefix tailTrace_1227504
  have hstable : (prefixWord ++ tailWord_1227504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227504).length < 2 ^ (prefixWord ++ tailWord_1227504).sum := by decide
  have hdescent : baseEnd_1227504 < baseStart_1227504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227551 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 6]
def baseStart_1227551 : Nat := 118140960795 + 1227551 * 2 ^ 59
def prefixEnd_1227551 : Nat := 4983230072969 + 3 ^ 40 * 1227551 * 2
def baseEnd_1227551 : Nat := 140071931312762652170467

theorem tailTrace_1227551 : CollatzResearch.WordTrace tailWord_1227551 prefixEnd_1227551 140071931312762652170467 := by
  unfold tailWord_1227551
  simp only [CollatzResearch.WordTrace]
  refine ⟨44772463175799850864898507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29848308783866567243265671 44772463175799850864898507)
  ·
    refine ⟨67158694763699776297347761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44772463175799850864898507 67158694763699776297347761)
    ·
      refine ⟨50369021072774832223010821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67158694763699776297347761 50369021072774832223010821)
      ·
        refine ⟨9444191451145281041814529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50369021072774832223010821 9444191451145281041814529)
        ·
          refine ⟨7083143588358960781360897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9444191451145281041814529 7083143588358960781360897)
          ·
            refine ⟨5312357691269220586020673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7083143588358960781360897 5312357691269220586020673)
            ·
              refine ⟨3984268268451915439515505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5312357691269220586020673 3984268268451915439515505)
              ·
                refine ⟨2988201201338936579636629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3984268268451915439515505 2988201201338936579636629)
                ·
                  refine ⟨140071931312762652170467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2988201201338936579636629 140071931312762652170467)
                  ·
                    rfl

theorem cell22_1227551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 6].length) (baseStart_1227551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227551 prefixEnd_1227551 := by exact prefixLift 1227551
  have htrace : WordTrace (prefixWord ++ tailWord_1227551) baseStart_1227551 baseEnd_1227551 := by
    simpa [prefixWord, tailWord_1227551, baseEnd_1227551] using wordTrace_append hprefix tailTrace_1227551
  have hstable : (prefixWord ++ tailWord_1227551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227551).length < 2 ^ (prefixWord ++ tailWord_1227551).sum := by decide
  have hdescent : baseEnd_1227551 < baseStart_1227551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227553 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_1227553 : Nat := 118140960795 + 1227553 * 2 ^ 59
def prefixEnd_1227553 : Nat := 4983230072969 + 3 ^ 40 * 1227553 * 2
def baseEnd_1227553 : Nat := 420216478579160617961395

theorem tailTrace_1227553 : CollatzResearch.WordTrace tailWord_1227553 prefixEnd_1227553 420216478579160617961395 := by
  unfold tailWord_1227553
  simp only [CollatzResearch.WordTrace]
  refine ⟨44772536121792605206471313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29848357414528403470980875 44772536121792605206471313)
  ·
    refine ⟨33579402091344453904853485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44772536121792605206471313 33579402091344453904853485)
    ·
      refine ⟨12592275784254170214320057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33579402091344453904853485 12592275784254170214320057)
      ·
        refine ⟨9444206838190627660740043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12592275784254170214320057 9444206838190627660740043)
        ·
          refine ⟨14166310257285941491110065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9444206838190627660740043 14166310257285941491110065)
          ·
            refine ⟨10624732692964456118332549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14166310257285941491110065 10624732692964456118332549)
            ·
              refine ⟨1992137379930835522187353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10624732692964456118332549 1992137379930835522187353)
              ·
                refine ⟨1494103034948126641640515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1992137379930835522187353 1494103034948126641640515)
                ·
                  refine ⟨2241154552422189962460773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494103034948126641640515 2241154552422189962460773)
                  ·
                    refine ⟨420216478579160617961395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2241154552422189962460773 420216478579160617961395)
                    ·
                      rfl

theorem cell22_1227553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_1227553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227553 prefixEnd_1227553 := by exact prefixLift 1227553
  have htrace : WordTrace (prefixWord ++ tailWord_1227553) baseStart_1227553 baseEnd_1227553 := by
    simpa [prefixWord, tailWord_1227553, baseEnd_1227553] using wordTrace_append hprefix tailTrace_1227553
  have hstable : (prefixWord ++ tailWord_1227553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227553).length < 2 ^ (prefixWord ++ tailWord_1227553).sum := by decide
  have hdescent : baseEnd_1227553 < baseStart_1227553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227583 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 4, 3]
def baseStart_1227583 : Nat := 118140960795 + 1227583 * 2 ^ 59
def prefixEnd_1227583 : Nat := 4983230072969 + 3 ^ 40 * 1227583 * 2
def baseEnd_1227583 : Nat := 420226748192250539711303

theorem tailTrace_1227583 : CollatzResearch.WordTrace tailWord_1227583 prefixEnd_1227583 420226748192250539711303 := by
  unfold tailWord_1227583
  simp only [CollatzResearch.WordTrace]
  refine ⟨44773630311683920330063403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29849086874455946886708935 44773630311683920330063403)
  ·
    refine ⟨67160445467525880495095105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44773630311683920330063403 67160445467525880495095105)
    ·
      refine ⟨50370334100644410371321329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67160445467525880495095105 50370334100644410371321329)
      ·
        refine ⟨37777750575483307778490997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50370334100644410371321329 37777750575483307778490997)
        ·
          refine ⟨3541664116451560104233531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37777750575483307778490997 3541664116451560104233531)
          ·
            refine ⟨5312496174677340156350297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541664116451560104233531 5312496174677340156350297)
            ·
              refine ⟨3984372131008005117262723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5312496174677340156350297 3984372131008005117262723)
              ·
                refine ⟨5976558196512007675894085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3984372131008005117262723 5976558196512007675894085)
                ·
                  refine ⟨1120604661846001439230141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5976558196512007675894085 1120604661846001439230141)
                  ·
                    refine ⟨420226748192250539711303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1120604661846001439230141 420226748192250539711303)
                    ·
                      rfl

theorem cell22_1227583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_1227583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227583 prefixEnd_1227583 := by exact prefixLift 1227583
  have htrace : WordTrace (prefixWord ++ tailWord_1227583) baseStart_1227583 baseEnd_1227583 := by
    simpa [prefixWord, tailWord_1227583, baseEnd_1227583] using wordTrace_append hprefix tailTrace_1227583
  have hstable : (prefixWord ++ tailWord_1227583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227583).length < 2 ^ (prefixWord ++ tailWord_1227583).sum := by decide
  have hdescent : baseEnd_1227583 < baseStart_1227583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227596 : List Nat := [2, 2, 1, 3, 3, 1, 1, 9]
def baseStart_1227596 : Nat := 118140960795 + 1227596 * 2 ^ 59
def prefixEnd_1227596 : Nat := 4983230072969 + 3 ^ 40 * 1227596 * 2
def baseEnd_1227596 : Nat := 46692355373102537681807

theorem tailTrace_1227596 : CollatzResearch.WordTrace tailWord_1227596 prefixEnd_1227596 46692355373102537681807 := by
  unfold tailWord_1227596
  simp only [CollatzResearch.WordTrace]
  refine ⟨22387052230318411775143321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29849402973757882366857761 22387052230318411775143321)
  ·
    refine ⟨16790289172738808831357491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22387052230318411775143321 16790289172738808831357491)
    ·
      refine ⟨25185433759108213247036237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16790289172738808831357491 25185433759108213247036237)
      ·
        refine ⟨9444537659665579967638589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25185433759108213247036237 9444537659665579967638589)
        ·
          refine ⟨3541701622374592487864471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9444537659665579967638589 3541701622374592487864471)
          ·
            refine ⟨5312552433561888731796707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541701622374592487864471 5312552433561888731796707)
            ·
              refine ⟨7968828650342833097695061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5312552433561888731796707 7968828650342833097695061)
              ·
                refine ⟨46692355373102537681807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7968828650342833097695061 46692355373102537681807)
                ·
                  rfl

theorem cell22_1227596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 9].length) (baseStart_1227596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227596 prefixEnd_1227596 := by exact prefixLift 1227596
  have htrace : WordTrace (prefixWord ++ tailWord_1227596) baseStart_1227596 baseEnd_1227596 := by
    simpa [prefixWord, tailWord_1227596, baseEnd_1227596] using wordTrace_append hprefix tailTrace_1227596
  have hstable : (prefixWord ++ tailWord_1227596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227596).length < 2 ^ (prefixWord ++ tailWord_1227596).sum := by decide
  have hdescent : baseEnd_1227596 < baseStart_1227596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227600 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 2, 3]
def baseStart_1227600 : Nat := 118140960795 + 1227600 * 2 ^ 59
def prefixEnd_1227600 : Nat := 4983230072969 + 3 ^ 40 * 1227600 * 2
def baseEnd_1227600 : Nat := 420232567639668162036251

theorem tailTrace_1227600 : CollatzResearch.WordTrace tailWord_1227600 prefixEnd_1227600 420232567639668162036251 := by
  unfold tailWord_1227600
  simp only [CollatzResearch.WordTrace]
  refine ⟨22387125176311166116716127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29849500235081554822288169 22387125176311166116716127)
  ·
    refine ⟨33580687764466749175074191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22387125176311166116716127 33580687764466749175074191)
    ·
      refine ⟨50371031646700123762611287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33580687764466749175074191 50371031646700123762611287)
      ·
        refine ⟨75556547470050185643916931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50371031646700123762611287 75556547470050185643916931)
        ·
          refine ⟨113334821205075278465875397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75556547470050185643916931 113334821205075278465875397)
          ·
            refine ⟨21250278975951614712351637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113334821205075278465875397 21250278975951614712351637)
            ·
              refine ⟨996106826997731939641483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21250278975951614712351637 996106826997731939641483)
              ·
                refine ⟨1494160240496597909462225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996106826997731939641483 1494160240496597909462225)
                ·
                  refine ⟨1120620180372448432096669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1494160240496597909462225 1120620180372448432096669)
                  ·
                    refine ⟨420232567639668162036251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1120620180372448432096669 420232567639668162036251)
                    ·
                      rfl

theorem cell22_1227600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 3].length) (baseStart_1227600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227600 prefixEnd_1227600 := by exact prefixLift 1227600
  have htrace : WordTrace (prefixWord ++ tailWord_1227600) baseStart_1227600 baseEnd_1227600 := by
    simpa [prefixWord, tailWord_1227600, baseEnd_1227600] using wordTrace_append hprefix tailTrace_1227600
  have hstable : (prefixWord ++ tailWord_1227600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227600).length < 2 ^ (prefixWord ++ tailWord_1227600).sum := by decide
  have hdescent : baseEnd_1227600 < baseStart_1227600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227737 : List Nat := [1, 2, 1, 2, 5, 3, 1, 3, 4]
def baseStart_1227737 : Nat := 118140960795 + 1227737 * 2 ^ 59
def prefixEnd_1227737 : Nat := 4983230072969 + 3 ^ 40 * 1227737 * 2
def baseEnd_1227737 : Nat := 140093155179815157120277

theorem tailTrace_1227737 : CollatzResearch.WordTrace tailWord_1227737 prefixEnd_1227737 140093155179815157120277 := by
  unfold tailWord_1227737
  simp only [CollatzResearch.WordTrace]
  refine ⟨44779247153126004631169465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29852831435417336420779643 44779247153126004631169465)
  ·
    refine ⟨33584435364844503473377099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44779247153126004631169465 33584435364844503473377099)
    ·
      refine ⟨50376653047266755210065649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33584435364844503473377099 50376653047266755210065649)
      ·
        refine ⟨37782489785450066407549237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50376653047266755210065649 37782489785450066407549237)
        ·
          refine ⟨3542108417385943725707741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37782489785450066407549237 3542108417385943725707741)
          ·
            refine ⟨1328290656519728897140403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3542108417385943725707741 1328290656519728897140403)
            ·
              refine ⟨1992435984779593345710605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328290656519728897140403 1992435984779593345710605)
              ·
                refine ⟨747163494292347504641477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1992435984779593345710605 747163494292347504641477)
                ·
                  refine ⟨140093155179815157120277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 747163494292347504641477 140093155179815157120277)
                  ·
                    rfl

theorem cell22_1227737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 4].length) (baseStart_1227737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227737 prefixEnd_1227737 := by exact prefixLift 1227737
  have htrace : WordTrace (prefixWord ++ tailWord_1227737) baseStart_1227737 baseEnd_1227737 := by
    simpa [prefixWord, tailWord_1227737, baseEnd_1227737] using wordTrace_append hprefix tailTrace_1227737
  have hstable : (prefixWord ++ tailWord_1227737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227737).length < 2 ^ (prefixWord ++ tailWord_1227737).sum := by decide
  have hdescent : baseEnd_1227737 < baseStart_1227737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227810 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_1227810 : Nat := 118140960795 + 1227810 * 2 ^ 59
def prefixEnd_1227810 : Nat := 4983230072969 + 3 ^ 40 * 1227810 * 2
def baseEnd_1227810 : Nat := 140101484977099204761869

theorem tailTrace_1227810 : CollatzResearch.WordTrace tailWord_1227810 prefixEnd_1227810 140101484977099204761869 := by
  unfold tailWord_1227810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11195477420465384524644221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29854606454574358732384589 11195477420465384524644221)
  ·
    refine ⟨4198304032674519196741583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11195477420465384524644221 4198304032674519196741583)
    ·
      refine ⟨6297456049011778795112375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4198304032674519196741583 6297456049011778795112375)
      ·
        refine ⟨9446184073517668192668563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6297456049011778795112375 9446184073517668192668563)
        ·
          refine ⟨14169276110276502289002845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9446184073517668192668563 14169276110276502289002845)
          ·
            refine ⟨5313478541353688358376067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14169276110276502289002845 5313478541353688358376067)
            ·
              refine ⟨7970217812030532537564101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313478541353688358376067 7970217812030532537564101)
              ·
                refine ⟨1494415839755724850793269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7970217812030532537564101 1494415839755724850793269)
                ·
                  refine ⟨140101484977099204761869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1494415839755724850793269 140101484977099204761869)
                  ·
                    rfl

theorem cell22_1227810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_1227810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227810 prefixEnd_1227810 := by exact prefixLift 1227810
  have htrace : WordTrace (prefixWord ++ tailWord_1227810) baseStart_1227810 baseEnd_1227810 := by
    simpa [prefixWord, tailWord_1227810, baseEnd_1227810] using wordTrace_append hprefix tailTrace_1227810
  have hstable : (prefixWord ++ tailWord_1227810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227810).length < 2 ^ (prefixWord ++ tailWord_1227810).sum := by decide
  have hdescent : baseEnd_1227810 < baseStart_1227810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227840 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_1227840 : Nat := 118140960795 + 1227840 * 2 ^ 59
def prefixEnd_1227840 : Nat := 4983230072969 + 3 ^ 40 * 1227840 * 2
def baseEnd_1227840 : Nat := 420314724544387536035515

theorem tailTrace_1227840 : CollatzResearch.WordTrace tailWord_1227840 prefixEnd_1227840 420314724544387536035515 := by
  unfold tailWord_1227840
  simp only [CollatzResearch.WordTrace]
  refine ⟨22391501935876426611084487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29855335914501902148112649 22391501935876426611084487)
  ·
    refine ⟨33587252903814639916626731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22391501935876426611084487 33587252903814639916626731)
    ·
      refine ⟨50380879355721959874940097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33587252903814639916626731 50380879355721959874940097)
      ·
        refine ⟨37785659516791469906205073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50380879355721959874940097 37785659516791469906205073)
        ·
          refine ⟨28339244637593602429653805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37785659516791469906205073 28339244637593602429653805)
          ·
            refine ⟨10627216739097600911120177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28339244637593602429653805 10627216739097600911120177)
            ·
              refine ⟨7970412554323200683340133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10627216739097600911120177 7970412554323200683340133)
              ·
                refine ⟨1494452353935600128126275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7970412554323200683340133 1494452353935600128126275)
                ·
                  refine ⟨2241678530903400192189413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494452353935600128126275 2241678530903400192189413)
                  ·
                    refine ⟨420314724544387536035515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2241678530903400192189413 420314724544387536035515)
                    ·
                      rfl

theorem cell22_1227840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_1227840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227840 prefixEnd_1227840 := by exact prefixLift 1227840
  have htrace : WordTrace (prefixWord ++ tailWord_1227840) baseStart_1227840 baseEnd_1227840 := by
    simpa [prefixWord, tailWord_1227840, baseEnd_1227840] using wordTrace_append hprefix tailTrace_1227840
  have hstable : (prefixWord ++ tailWord_1227840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227840).length < 2 ^ (prefixWord ++ tailWord_1227840).sum := by decide
  have hdescent : baseEnd_1227840 < baseStart_1227840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227857 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 1, 4]
def baseStart_1227857 : Nat := 118140960795 + 1227857 * 2 ^ 59
def prefixEnd_1227857 : Nat := 4983230072969 + 3 ^ 40 * 1227857 * 2
def baseEnd_1227857 : Nat := 420320543991805158360463

theorem tailTrace_1227857 : CollatzResearch.WordTrace tailWord_1227857 prefixEnd_1227857 420320543991805158360463 := by
  unfold tailWord_1227857
  simp only [CollatzResearch.WordTrace]
  refine ⟨44783623912691265125537825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29855749275127510083691883 44783623912691265125537825)
  ·
    refine ⟨33587717934518448844153369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44783623912691265125537825 33587717934518448844153369)
    ·
      refine ⟨25190788450888836633115027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33587717934518448844153369 25190788450888836633115027)
      ·
        refine ⟨37786182676333254949672541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25190788450888836633115027 37786182676333254949672541)
        ·
          refine ⟨14169818503624970606127203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37786182676333254949672541 14169818503624970606127203)
          ·
            refine ⟨21254727755437455909190805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14169818503624970606127203 21254727755437455909190805)
            ·
              refine ⟨996315363536130745743319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21254727755437455909190805 996315363536130745743319)
              ·
                refine ⟨1494473045304196118614979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996315363536130745743319 1494473045304196118614979)
                ·
                  refine ⟨2241709567956294177922469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494473045304196118614979 2241709567956294177922469)
                  ·
                    refine ⟨420320543991805158360463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2241709567956294177922469 420320543991805158360463)
                    ·
                      rfl

theorem cell22_1227857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_1227857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227857 prefixEnd_1227857 := by exact prefixLift 1227857
  have htrace : WordTrace (prefixWord ++ tailWord_1227857) baseStart_1227857 baseEnd_1227857 := by
    simpa [prefixWord, tailWord_1227857, baseEnd_1227857] using wordTrace_append hprefix tailTrace_1227857
  have hstable : (prefixWord ++ tailWord_1227857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227857).length < 2 ^ (prefixWord ++ tailWord_1227857).sum := by decide
  have hdescent : baseEnd_1227857 < baseStart_1227857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227885 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1227885 : Nat := 118140960795 + 1227885 * 2 ^ 59
def prefixEnd_1227885 : Nat := 4983230072969 + 3 ^ 40 * 1227885 * 2
def baseEnd_1227885 : Nat := 420330128964022418660377

theorem tailTrace_1227885 : CollatzResearch.WordTrace tailWord_1227885 prefixEnd_1227885 420330128964022418660377 := by
  unfold tailWord_1227885
  simp only [CollatzResearch.WordTrace]
  refine ⟨44784645156589825907557109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29856430104393217271704739 44784645156589825907557109)
  ·
    refine ⟨4198560483430296178833479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44784645156589825907557109 4198560483430296178833479)
    ·
      refine ⟨6297840725145444268250219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4198560483430296178833479 6297840725145444268250219)
      ·
        refine ⟨9446761087718166402375329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6297840725145444268250219 9446761087718166402375329)
        ·
          refine ⟨7085070815788624801781497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9446761087718166402375329 7085070815788624801781497)
          ·
            refine ⟨5313803111841468601336123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7085070815788624801781497 5313803111841468601336123)
            ·
              refine ⟨7970704667762202902004185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5313803111841468601336123 7970704667762202902004185)
              ·
                refine ⟨5978028500821652176503139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7970704667762202902004185 5978028500821652176503139)
                ·
                  refine ⟨8967042751232478264754709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5978028500821652176503139 8967042751232478264754709)
                  ·
                    refine ⟨420330128964022418660377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8967042751232478264754709 420330128964022418660377)
                    ·
                      rfl

theorem cell22_1227885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1227885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227885 prefixEnd_1227885 := by exact prefixLift 1227885
  have htrace : WordTrace (prefixWord ++ tailWord_1227885) baseStart_1227885 baseEnd_1227885 := by
    simpa [prefixWord, tailWord_1227885, baseEnd_1227885] using wordTrace_append hprefix tailTrace_1227885
  have hstable : (prefixWord ++ tailWord_1227885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227885).length < 2 ^ (prefixWord ++ tailWord_1227885).sum := by decide
  have hdescent : baseEnd_1227885 < baseStart_1227885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227915 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 5, 3]
def baseStart_1227915 : Nat := 118140960795 + 1227915 * 2 ^ 59
def prefixEnd_1227915 : Nat := 4983230072969 + 3 ^ 40 * 1227915 * 2
def baseEnd_1227915 : Nat := 420340398577112340410285

theorem tailTrace_1227915 : CollatzResearch.WordTrace tailWord_1227915 prefixEnd_1227915 420340398577112340410285 := by
  unfold tailWord_1227915
  simp only [CollatzResearch.WordTrace]
  refine ⟨44785739346481141031149199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29857159564320760687432799 44785739346481141031149199)
  ·
    refine ⟨67178609019721711546723799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44785739346481141031149199 67178609019721711546723799)
    ·
      refine ⟨100767913529582567320085699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67178609019721711546723799 100767913529582567320085699)
      ·
        refine ⟨151151870294373850980128549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100767913529582567320085699 151151870294373850980128549)
        ·
          refine ⟨28340975680195097058774103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151151870294373850980128549 28340975680195097058774103)
          ·
            refine ⟨42511463520292645588161155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28340975680195097058774103 42511463520292645588161155)
            ·
              refine ⟨63767195280438968382241733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42511463520292645588161155 63767195280438968382241733)
              ·
                refine ⟨11956349115082306571670325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63767195280438968382241733 11956349115082306571670325)
                ·
                  refine ⟨1120907729538966241094093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11956349115082306571670325 1120907729538966241094093)
                  ·
                    refine ⟨420340398577112340410285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1120907729538966241094093 420340398577112340410285)
                    ·
                      rfl

theorem cell22_1227915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 3].length) (baseStart_1227915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227915 prefixEnd_1227915 := by exact prefixLift 1227915
  have htrace : WordTrace (prefixWord ++ tailWord_1227915) baseStart_1227915 baseEnd_1227915 := by
    simpa [prefixWord, tailWord_1227915, baseEnd_1227915] using wordTrace_append hprefix tailTrace_1227915
  have hstable : (prefixWord ++ tailWord_1227915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227915).length < 2 ^ (prefixWord ++ tailWord_1227915).sum := by decide
  have hdescent : baseEnd_1227915 < baseStart_1227915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1227938 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1227938 : Nat := 118140960795 + 1227938 * 2 ^ 59
def prefixEnd_1227938 : Nat := 4983230072969 + 3 ^ 40 * 1227938 * 2
def baseEnd_1227938 : Nat := 420348271947147947085215

theorem tailTrace_1227938 : CollatzResearch.WordTrace tailWord_1227938 prefixEnd_1227938 420348271947147947085215 := by
  unfold tailWord_1227938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196644556349453989809117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29857718816931877306157645 11196644556349453989809117)
  ·
    refine ⟨4198741708631045246178419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11196644556349453989809117 4198741708631045246178419)
    ·
      refine ⟨6298112562946567869267629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4198741708631045246178419 6298112562946567869267629)
      ·
        refine ⟨2361792211104962950975361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6298112562946567869267629 2361792211104962950975361)
        ·
          refine ⟨1771344158328722213231521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2361792211104962950975361 1771344158328722213231521)
          ·
            refine ⟨1328508118746541659923641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1771344158328722213231521 1328508118746541659923641)
            ·
              refine ⟨996381089059906244942731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328508118746541659923641 996381089059906244942731)
              ·
                refine ⟨1494571633589859367414097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996381089059906244942731 1494571633589859367414097)
                ·
                  refine ⟨1120928725192394525560573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1494571633589859367414097 1120928725192394525560573)
                  ·
                    refine ⟨420348271947147947085215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1120928725192394525560573 420348271947147947085215)
                    ·
                      rfl

theorem cell22_1227938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1227938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1227938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1227938 prefixEnd_1227938 := by exact prefixLift 1227938
  have htrace : WordTrace (prefixWord ++ tailWord_1227938) baseStart_1227938 baseEnd_1227938 := by
    simpa [prefixWord, tailWord_1227938, baseEnd_1227938] using wordTrace_append hprefix tailTrace_1227938
  have hstable : (prefixWord ++ tailWord_1227938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1227938).length < 2 ^ (prefixWord ++ tailWord_1227938).sum := by decide
  have hdescent : baseEnd_1227938 < baseStart_1227938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1227938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228035 : List Nat := [1, 1, 1, 3, 2, 5, 9]
def baseStart_1228035 : Nat := 118140960795 + 1228035 * 2 ^ 59
def prefixEnd_1228035 : Nat := 4983230072969 + 3 ^ 40 * 1228035 * 2
def baseEnd_1228035 : Nat := 15569684334424889904071

theorem tailTrace_1228035 : CollatzResearch.WordTrace tailWord_1228035 prefixEnd_1228035 15569684334424889904071 := by
  unfold tailWord_1228035
  simp only [CollatzResearch.WordTrace]
  refine ⟨44790116106046401525517559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29860077404030934350345039 44790116106046401525517559)
  ·
    refine ⟨67185174159069602288276339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44790116106046401525517559 67185174159069602288276339)
    ·
      refine ⟨100777761238604403432414509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67185174159069602288276339 100777761238604403432414509)
      ·
        refine ⟨37791660464476651287155441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100777761238604403432414509 37791660464476651287155441)
        ·
          refine ⟨28343745348357488465366581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37791660464476651287155441 28343745348357488465366581)
          ·
            refine ⟨2657226126408514543628117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28343745348357488465366581 2657226126408514543628117)
            ·
              refine ⟨15569684334424889904071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2657226126408514543628117 15569684334424889904071)
              ·
                rfl

theorem cell22_1228035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 9].length) (baseStart_1228035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228035 prefixEnd_1228035 := by exact prefixLift 1228035
  have htrace : WordTrace (prefixWord ++ tailWord_1228035) baseStart_1228035 baseEnd_1228035 := by
    simpa [prefixWord, tailWord_1228035, baseEnd_1228035] using wordTrace_append hprefix tailTrace_1228035
  have hstable : (prefixWord ++ tailWord_1228035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228035).length < 2 ^ (prefixWord ++ tailWord_1228035).sum := by decide
  have hdescent : baseEnd_1228035 < baseStart_1228035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228056 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 2, 3]
def baseStart_1228056 : Nat := 118140960795 + 1228056 * 2 ^ 59
def prefixEnd_1228056 : Nat := 4983230072969 + 3 ^ 40 * 1228056 * 2
def baseEnd_1228056 : Nat := 420388665758634972634853

theorem tailTrace_1228056 : CollatzResearch.WordTrace tailWord_1228056 prefixEnd_1228056 420388665758634972634853 := by
  unfold tailWord_1228056
  simp only [CollatzResearch.WordTrace]
  refine ⟨22395441019485161056016011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29860588025980214741354681 22395441019485161056016011)
  ·
    refine ⟨33593161529227741584024017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22395441019485161056016011 33593161529227741584024017)
    ·
      refine ⟨25194871146920806188018013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33593161529227741584024017 25194871146920806188018013)
      ·
        refine ⟨9448076680095302320506755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25194871146920806188018013 9448076680095302320506755)
        ·
          refine ⟨14172115020142953480760133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9448076680095302320506755 14172115020142953480760133)
          ·
            refine ⟨2657271566276803777642525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14172115020142953480760133 2657271566276803777642525)
            ·
              refine ⟨996476837353801416615947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2657271566276803777642525 996476837353801416615947)
              ·
                refine ⟨1494715256030702124923921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996476837353801416615947 1494715256030702124923921)
                ·
                  refine ⟨1121036442023026593692941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1494715256030702124923921 1121036442023026593692941)
                  ·
                    refine ⟨420388665758634972634853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121036442023026593692941 420388665758634972634853)
                    ·
                      rfl

theorem cell22_1228056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_1228056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228056 prefixEnd_1228056 := by exact prefixLift 1228056
  have htrace : WordTrace (prefixWord ++ tailWord_1228056) baseStart_1228056 baseEnd_1228056 := by
    simpa [prefixWord, tailWord_1228056, baseEnd_1228056] using wordTrace_append hprefix tailTrace_1228056
  have hstable : (prefixWord ++ tailWord_1228056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228056).length < 2 ^ (prefixWord ++ tailWord_1228056).sum := by decide
  have hdescent : baseEnd_1228056 < baseStart_1228056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228069 : List Nat := [1, 3, 1, 2, 4, 3, 2, 6]
def baseStart_1228069 : Nat := 118140960795 + 1228069 * 2 ^ 59
def prefixEnd_1228069 : Nat := 4983230072969 + 3 ^ 40 * 1228069 * 2
def baseEnd_1228069 : Nat := 46710346213811919117757

theorem tailTrace_1228069 : CollatzResearch.WordTrace tailWord_1228069 prefixEnd_1228069 46710346213811919117757 := by
  unfold tailWord_1228069
  simp only [CollatzResearch.WordTrace]
  refine ⟨44791356187923225332255261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29860904125282150221503507 44791356187923225332255261)
  ·
    refine ⟨16796758570471209499595723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44791356187923225332255261 16796758570471209499595723)
    ·
      refine ⟨25195137855706814249393585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16796758570471209499595723 25195137855706814249393585)
      ·
        refine ⟨18896353391780110687045189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25195137855706814249393585 18896353391780110687045189)
        ·
          refine ⟨3543066260958770753820973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18896353391780110687045189 3543066260958770753820973)
          ·
            refine ⟨1328649847859539032682865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3543066260958770753820973 1328649847859539032682865)
            ·
              refine ⟨996487385894654274512149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328649847859539032682865 996487385894654274512149)
              ·
                refine ⟨46710346213811919117757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 996487385894654274512149 46710346213811919117757)
                ·
                  rfl

theorem cell22_1228069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 6].length) (baseStart_1228069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228069 prefixEnd_1228069 := by exact prefixLift 1228069
  have htrace : WordTrace (prefixWord ++ tailWord_1228069) baseStart_1228069 baseEnd_1228069 := by
    simpa [prefixWord, tailWord_1228069, baseEnd_1228069] using wordTrace_append hprefix tailTrace_1228069
  have hstable : (prefixWord ++ tailWord_1228069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228069).length < 2 ^ (prefixWord ++ tailWord_1228069).sum := by decide
  have hdescent : baseEnd_1228069 < baseStart_1228069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228080 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 9]
def baseStart_1228080 : Nat := 118140960795 + 1228080 * 2 ^ 59
def prefixEnd_1228080 : Nat := 4983230072969 + 3 ^ 40 * 1228080 * 2
def baseEnd_1228080 : Nat := 140132293816368970011593

theorem tailTrace_1228080 : CollatzResearch.WordTrace tailWord_1228080 prefixEnd_1228080 140132293816368970011593 := by
  unfold tailWord_1228080
  simp only [CollatzResearch.WordTrace]
  refine ⟨22395878695441687105452847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29861171593922249473937129 22395878695441687105452847)
  ·
    refine ⟨33593818043162530658179271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22395878695441687105452847 33593818043162530658179271)
    ·
      refine ⟨50390727064743795987268907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33593818043162530658179271 50390727064743795987268907)
      ·
        refine ⟨75586090597115693980903361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50390727064743795987268907 75586090597115693980903361)
        ·
          refine ⟨56689567947836770485677521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75586090597115693980903361 56689567947836770485677521)
          ·
            refine ⟨42517175960877577864258141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56689567947836770485677521 42517175960877577864258141)
            ·
              refine ⟨15943940985329091699096803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42517175960877577864258141 15943940985329091699096803)
              ·
                refine ⟨23915911477993637548645205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15943940985329091699096803 23915911477993637548645205)
                ·
                  refine ⟨140132293816368970011593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23915911477993637548645205 140132293816368970011593)
                  ·
                    rfl

theorem cell22_1228080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_1228080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228080 prefixEnd_1228080 := by exact prefixLift 1228080
  have htrace : WordTrace (prefixWord ++ tailWord_1228080) baseStart_1228080 baseEnd_1228080 := by
    simpa [prefixWord, tailWord_1228080, baseEnd_1228080] using wordTrace_append hprefix tailTrace_1228080
  have hstable : (prefixWord ++ tailWord_1228080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228080).length < 2 ^ (prefixWord ++ tailWord_1228080).sum := by decide
  have hdescent : baseEnd_1228080 < baseStart_1228080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228086 : List Nat := [5, 1, 2, 3, 1, 2, 8]
def baseStart_1228086 : Nat := 118140960795 + 1228086 * 2 ^ 59
def prefixEnd_1228086 : Nat := 4983230072969 + 3 ^ 40 * 1228086 * 2
def baseEnd_1228086 : Nat := 15570330939693514606843

theorem tailTrace_1228086 : CollatzResearch.WordTrace tailWord_1228086 prefixEnd_1228086 15570330939693514606843 := by
  unfold tailWord_1228086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799498514303852327226507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29861317485907758157082741 2799498514303852327226507)
  ·
    refine ⟨4199247771455778490839761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2799498514303852327226507 4199247771455778490839761)
    ·
      refine ⟨3149435828591833868129821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4199247771455778490839761 3149435828591833868129821)
      ·
        refine ⟨1181038435721937700548683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3149435828591833868129821 1181038435721937700548683)
        ·
          refine ⟨1771557653582906550823025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181038435721937700548683 1771557653582906550823025)
          ·
            refine ⟨1328668240187179913117269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1771557653582906550823025 1328668240187179913117269)
            ·
              refine ⟨15570330939693514606843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1328668240187179913117269 15570330939693514606843)
              ·
                rfl

theorem cell22_1228086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 8].length) (baseStart_1228086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228086 prefixEnd_1228086 := by exact prefixLift 1228086
  have htrace : WordTrace (prefixWord ++ tailWord_1228086) baseStart_1228086 baseEnd_1228086 := by
    simpa [prefixWord, tailWord_1228086, baseEnd_1228086] using wordTrace_append hprefix tailTrace_1228086
  have hstable : (prefixWord ++ tailWord_1228086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228086).length < 2 ^ (prefixWord ++ tailWord_1228086).sum := by decide
  have hdescent : baseEnd_1228086 < baseStart_1228086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228157 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_1228157 : Nat := 118140960795 + 1228157 * 2 ^ 59
def prefixEnd_1228157 : Nat := 4983230072969 + 3 ^ 40 * 1228157 * 2
def baseEnd_1228157 : Nat := 420423240122704375859543

theorem tailTrace_1228157 : CollatzResearch.WordTrace tailWord_1228157 prefixEnd_1228157 420423240122704375859543 := by
  unfold tailWord_1228157
  simp only [CollatzResearch.WordTrace]
  refine ⟨44794565811604416361458725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29863043874402944240972483 44794565811604416361458725)
  ·
    refine ⟨8398981089675828067773511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44794565811604416361458725 8398981089675828067773511)
    ·
      refine ⟨12598471634513742101660267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8398981089675828067773511 12598471634513742101660267)
      ·
        refine ⟨18897707451770613152490401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12598471634513742101660267 18897707451770613152490401)
        ·
          refine ⟨14173280588827959864367801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18897707451770613152490401 14173280588827959864367801)
          ·
            refine ⟨10629960441620969898275851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14173280588827959864367801 10629960441620969898275851)
            ·
              refine ⟨15944940662431454847413777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10629960441620969898275851 15944940662431454847413777)
              ·
                refine ⟨11958705496823591135560333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15944940662431454847413777 11958705496823591135560333)
                ·
                  refine ⟨4484514561308846675835125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11958705496823591135560333 4484514561308846675835125)
                  ·
                    refine ⟨420423240122704375859543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4484514561308846675835125 420423240122704375859543)
                    ·
                      rfl

theorem cell22_1228157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_1228157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228157 prefixEnd_1228157 := by exact prefixLift 1228157
  have htrace : WordTrace (prefixWord ++ tailWord_1228157) baseStart_1228157 baseEnd_1228157 := by
    simpa [prefixWord, tailWord_1228157, baseEnd_1228157] using wordTrace_append hprefix tailTrace_1228157
  have hstable : (prefixWord ++ tailWord_1228157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228157).length < 2 ^ (prefixWord ++ tailWord_1228157).sum := by decide
  have hdescent : baseEnd_1228157 < baseStart_1228157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228172 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_1228172 : Nat := 118140960795 + 1228172 * 2 ^ 59
def prefixEnd_1228172 : Nat := 4983230072969 + 3 ^ 40 * 1228172 * 2
def baseEnd_1228172 : Nat := 420428374929249336734497

theorem tailTrace_1228172 : CollatzResearch.WordTrace tailWord_1228172 prefixEnd_1228172 420428374929249336734497 := by
  unfold tailWord_1228172
  simp only [CollatzResearch.WordTrace]
  refine ⟨22397556453275036961627385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29863408604366715948836513 22397556453275036961627385)
  ·
    refine ⟨16798167339956277721220539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22397556453275036961627385 16798167339956277721220539)
    ·
      refine ⟨25197251009934416581830809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16798167339956277721220539 25197251009934416581830809)
      ·
        refine ⟨18897938257450812436373107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25197251009934416581830809 18897938257450812436373107)
        ·
          refine ⟨28346907386176218654559661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18897938257450812436373107 28346907386176218654559661)
          ·
            refine ⟨10630090269816081995459873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28346907386176218654559661 10630090269816081995459873)
            ·
              refine ⟨7972567702362061496594905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10630090269816081995459873 7972567702362061496594905)
              ·
                refine ⟨5979425776771546122446179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7972567702362061496594905 5979425776771546122446179)
                ·
                  refine ⟨8969138665157319183669269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5979425776771546122446179 8969138665157319183669269)
                  ·
                    refine ⟨420428374929249336734497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8969138665157319183669269 420428374929249336734497)
                    ·
                      rfl

theorem cell22_1228172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_1228172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228172 prefixEnd_1228172 := by exact prefixLift 1228172
  have htrace : WordTrace (prefixWord ++ tailWord_1228172) baseStart_1228172 baseEnd_1228172 := by
    simpa [prefixWord, tailWord_1228172, baseEnd_1228172] using wordTrace_append hprefix tailTrace_1228172
  have hstable : (prefixWord ++ tailWord_1228172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228172).length < 2 ^ (prefixWord ++ tailWord_1228172).sum := by decide
  have hdescent : baseEnd_1228172 < baseStart_1228172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228189 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_1228189 : Nat := 118140960795 + 1228189 * 2 ^ 59
def prefixEnd_1228189 : Nat := 4983230072969 + 3 ^ 40 * 1228189 * 2
def baseEnd_1228189 : Nat := 420434194376666959059445

theorem tailTrace_1228189 : CollatzResearch.WordTrace tailWord_1228189 prefixEnd_1228189 420434194376666959059445 := by
  unfold tailWord_1228189
  simp only [CollatzResearch.WordTrace]
  refine ⟨44795732947488485826623621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29863821964992323884415747 44795732947488485826623621)
  ·
    refine ⟨8399199927654091092491929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44795732947488485826623621 8399199927654091092491929)
    ·
      refine ⟨6299399945740568319368947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8399199927654091092491929 6299399945740568319368947)
      ·
        refine ⟨9449099918610852479053421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6299399945740568319368947 9449099918610852479053421)
        ·
          refine ⟨3543412469479069679645033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9449099918610852479053421 3543412469479069679645033)
          ·
            refine ⟨2657559352109302259733775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3543412469479069679645033 2657559352109302259733775)
            ·
              refine ⟨3986339028163953389600663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657559352109302259733775 3986339028163953389600663)
              ·
                refine ⟨5979508542245930084400995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3986339028163953389600663 5979508542245930084400995)
                ·
                  refine ⟨8969262813368895126601493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5979508542245930084400995 8969262813368895126601493)
                  ·
                    refine ⟨420434194376666959059445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8969262813368895126601493 420434194376666959059445)
                    ·
                      rfl

theorem cell22_1228189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_1228189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228189 prefixEnd_1228189 := by exact prefixLift 1228189
  have htrace : WordTrace (prefixWord ++ tailWord_1228189) baseStart_1228189 baseEnd_1228189 := by
    simpa [prefixWord, tailWord_1228189, baseEnd_1228189] using wordTrace_append hprefix tailTrace_1228189
  have hstable : (prefixWord ++ tailWord_1228189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228189).length < 2 ^ (prefixWord ++ tailWord_1228189).sum := by decide
  have hdescent : baseEnd_1228189 < baseStart_1228189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228236 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 3, 3]
def baseStart_1228236 : Nat := 118140960795 + 1228236 * 2 ^ 59
def prefixEnd_1228236 : Nat := 4983230072969 + 3 ^ 40 * 1228236 * 2
def baseEnd_1228236 : Nat := 420450283437174503134301

theorem tailTrace_1228236 : CollatzResearch.WordTrace tailWord_1228236 prefixEnd_1228236 420450283437174503134301 := by
  unfold tailWord_1228236
  simp only [CollatzResearch.WordTrace]
  refine ⟨22398723589159106426792281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29864964785545475235723041 22398723589159106426792281)
  ·
    refine ⟨16799042691869329820094211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22398723589159106426792281 16799042691869329820094211)
    ·
      refine ⟨25198564037803994730141317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16799042691869329820094211 25198564037803994730141317)
      ·
        refine ⟨4724730757088249011901497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25198564037803994730141317 4724730757088249011901497)
        ·
          refine ⟨3543548067816186758926123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4724730757088249011901497 3543548067816186758926123)
          ·
            refine ⟨5315322101724280138389185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543548067816186758926123 5315322101724280138389185)
            ·
              refine ⟨3986491576293210103791889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5315322101724280138389185 3986491576293210103791889)
              ·
                refine ⟨2989868682219907577843917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3986491576293210103791889 2989868682219907577843917)
                ·
                  refine ⟨1121200755832465341691469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2989868682219907577843917 1121200755832465341691469)
                  ·
                    refine ⟨420450283437174503134301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121200755832465341691469 420450283437174503134301)
                    ·
                      rfl

theorem cell22_1228236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_1228236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228236 prefixEnd_1228236 := by exact prefixLift 1228236
  have htrace : WordTrace (prefixWord ++ tailWord_1228236) baseStart_1228236 baseEnd_1228236 := by
    simpa [prefixWord, tailWord_1228236, baseEnd_1228236] using wordTrace_append hprefix tailTrace_1228236
  have hstable : (prefixWord ++ tailWord_1228236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228236).length < 2 ^ (prefixWord ++ tailWord_1228236).sum := by decide
  have hdescent : baseEnd_1228236 < baseStart_1228236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228247 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 1, 7]
def baseStart_1228247 : Nat := 118140960795 + 1228247 * 2 ^ 59
def prefixEnd_1228247 : Nat := 4983230072969 + 3 ^ 40 * 1228247 * 2
def baseEnd_1228247 : Nat := 420454048961974141109267

theorem tailTrace_1228247 : CollatzResearch.WordTrace tailWord_1228247 prefixEnd_1228247 420454048961974141109267 := by
  unfold tailWord_1228247
  simp only [CollatzResearch.WordTrace]
  refine ⟨44797848381278361732234995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29865232254185574488156663 44797848381278361732234995)
  ·
    refine ⟨67196772571917542598352493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44797848381278361732234995 67196772571917542598352493)
    ·
      refine ⟨25198789714469078474382185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67196772571917542598352493 25198789714469078474382185)
      ·
        refine ⟨18899092285851808855786639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25198789714469078474382185 18899092285851808855786639)
        ·
          refine ⟨28348638428777713283679959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18899092285851808855786639 28348638428777713283679959)
          ·
            refine ⟨42522957643166569925519939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28348638428777713283679959 42522957643166569925519939)
            ·
              refine ⟨63784436464749854888279909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42522957643166569925519939 63784436464749854888279909)
              ·
                refine ⟨11959581837140597791552483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63784436464749854888279909 11959581837140597791552483)
                ·
                  refine ⟨17939372755710896687328725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11959581837140597791552483 17939372755710896687328725)
                  ·
                    refine ⟨420454048961974141109267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17939372755710896687328725 420454048961974141109267)
                    ·
                      rfl

theorem cell22_1228247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_1228247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228247 prefixEnd_1228247 := by exact prefixLift 1228247
  have htrace : WordTrace (prefixWord ++ tailWord_1228247) baseStart_1228247 baseEnd_1228247 := by
    simpa [prefixWord, tailWord_1228247, baseEnd_1228247] using wordTrace_append hprefix tailTrace_1228247
  have hstable : (prefixWord ++ tailWord_1228247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228247).length < 2 ^ (prefixWord ++ tailWord_1228247).sum := by decide
  have hdescent : baseEnd_1228247 < baseStart_1228247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228270 : List Nat := [4, 1, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1228270 : Nat := 118140960795 + 1228270 * 2 ^ 59
def prefixEnd_1228270 : Nat := 4983230072969 + 3 ^ 40 * 1228270 * 2
def baseEnd_1228270 : Nat := 420461922332009747784197

theorem tailTrace_1228270 : CollatzResearch.WordTrace tailWord_1228270 prefixEnd_1228270 420461922332009747784197 := by
  unfold tailWord_1228270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5599835907524379582540283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29865791506796691106881509 5599835907524379582540283)
  ·
    refine ⟨8399753861286569373810425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5599835907524379582540283 8399753861286569373810425)
    ·
      refine ⟨6299815395964927030357819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8399753861286569373810425 6299815395964927030357819)
      ·
        refine ⟨9449723093947390545536729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6299815395964927030357819 9449723093947390545536729)
        ·
          refine ⟨7087292320460542909152547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9449723093947390545536729 7087292320460542909152547)
          ·
            refine ⟨10630938480690814363728821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087292320460542909152547 10630938480690814363728821)
            ·
              refine ⟨996650482564763846599577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10630938480690814363728821 996650482564763846599577)
              ·
                refine ⟨747487861923572884949683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996650482564763846599577 747487861923572884949683)
                ·
                  refine ⟨1121231792885359327424525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747487861923572884949683 1121231792885359327424525)
                  ·
                    refine ⟨420461922332009747784197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121231792885359327424525 420461922332009747784197)
                    ·
                      rfl

theorem cell22_1228270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1228270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228270 prefixEnd_1228270 := by exact prefixLift 1228270
  have htrace : WordTrace (prefixWord ++ tailWord_1228270) baseStart_1228270 baseEnd_1228270 := by
    simpa [prefixWord, tailWord_1228270, baseEnd_1228270] using wordTrace_append hprefix tailTrace_1228270
  have hstable : (prefixWord ++ tailWord_1228270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228270).length < 2 ^ (prefixWord ++ tailWord_1228270).sum := by decide
  have hdescent : baseEnd_1228270 < baseStart_1228270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228296 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_1228296 : Nat := 118140960795 + 1228296 * 2 ^ 59
def prefixEnd_1228296 : Nat := 4983230072969 + 3 ^ 40 * 1228296 * 2
def baseEnd_1228296 : Nat := 420470822663354346634117

theorem tailTrace_1228296 : CollatzResearch.WordTrace tailWord_1228296 prefixEnd_1228296 420470822663354346634117 := by
  unfold tailWord_1228296
  simp only [CollatzResearch.WordTrace]
  refine ⟨22399817779050421550384371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29866423705400562067179161 22399817779050421550384371)
  ·
    refine ⟨33599726668575632325576557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22399817779050421550384371 33599726668575632325576557)
    ·
      refine ⟨12599897500715862122091209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33599726668575632325576557 12599897500715862122091209)
      ·
        refine ⟨9449923125536896591568407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12599897500715862122091209 9449923125536896591568407)
        ·
          refine ⟨14174884688305344887352611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9449923125536896591568407 14174884688305344887352611)
          ·
            refine ⟨21262327032458017331028917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14174884688305344887352611 21262327032458017331028917)
            ·
              refine ⟨1993343159292939124783961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21262327032458017331028917 1993343159292939124783961)
              ·
                refine ⟨1495007369469704343587971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1993343159292939124783961 1495007369469704343587971)
                ·
                  refine ⟨2242511054204556515381957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495007369469704343587971 2242511054204556515381957)
                  ·
                    refine ⟨420470822663354346634117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2242511054204556515381957 420470822663354346634117)
                    ·
                      rfl

theorem cell22_1228296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_1228296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228296 prefixEnd_1228296 := by exact prefixLift 1228296
  have htrace : WordTrace (prefixWord ++ tailWord_1228296) baseStart_1228296 baseEnd_1228296 := by
    simpa [prefixWord, tailWord_1228296, baseEnd_1228296] using wordTrace_append hprefix tailTrace_1228296
  have hstable : (prefixWord ++ tailWord_1228296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228296).length < 2 ^ (prefixWord ++ tailWord_1228296).sum := by decide
  have hdescent : baseEnd_1228296 < baseStart_1228296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228309 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1228309 : Nat := 118140960795 + 1228309 * 2 ^ 59
def prefixEnd_1228309 : Nat := 4983230072969 + 3 ^ 40 * 1228309 * 2
def baseEnd_1228309 : Nat := 420475272829026646059077

theorem tailTrace_1228309 : CollatzResearch.WordTrace tailWord_1228309 prefixEnd_1228309 420475272829026646059077 := by
  unfold tailWord_1228309
  simp only [CollatzResearch.WordTrace]
  refine ⟨44800109707053746320991981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29866739804702497547327987 44800109707053746320991981)
  ·
    refine ⟨16800041140145154870371993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44800109707053746320991981 16800041140145154870371993)
    ·
      refine ⟨12600030855108866152778995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16800041140145154870371993 12600030855108866152778995)
      ·
        refine ⟨18900046282663299229168493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12600030855108866152778995 18900046282663299229168493)
        ·
          refine ⟨7087517355998737210938185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18900046282663299229168493 7087517355998737210938185)
          ·
            refine ⟨5315638016999052908203639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7087517355998737210938185 5315638016999052908203639)
            ·
              refine ⟨7973457025498579362305459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5315638016999052908203639 7973457025498579362305459)
              ·
                refine ⟨11960185538247869043458189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7973457025498579362305459 11960185538247869043458189)
                ·
                  refine ⟨4485069576842950891296821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11960185538247869043458189 4485069576842950891296821)
                  ·
                    refine ⟨420475272829026646059077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4485069576842950891296821 420475272829026646059077)
                    ·
                      rfl

theorem cell22_1228309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1228309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228309 prefixEnd_1228309 := by exact prefixLift 1228309
  have htrace : WordTrace (prefixWord ++ tailWord_1228309) baseStart_1228309 baseEnd_1228309 := by
    simpa [prefixWord, tailWord_1228309, baseEnd_1228309] using wordTrace_append hprefix tailTrace_1228309
  have hstable : (prefixWord ++ tailWord_1228309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228309).length < 2 ^ (prefixWord ++ tailWord_1228309).sum := by decide
  have hdescent : baseEnd_1228309 < baseStart_1228309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228339 : List Nat := [1, 1, 1, 2, 4, 3, 3, 7]
def baseStart_1228339 : Nat := 118140960795 + 1228339 * 2 ^ 59
def prefixEnd_1228339 : Nat := 4983230072969 + 3 ^ 40 * 1228339 * 2
def baseEnd_1228339 : Nat := 46720615826901840867665

theorem tailTrace_1228339 : CollatzResearch.WordTrace tailWord_1228339 prefixEnd_1228339 46720615826901840867665 := by
  unfold tailWord_1228339
  simp only [CollatzResearch.WordTrace]
  refine ⟨44801203896945061444584071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29867469264630040963056047 44801203896945061444584071)
  ·
    refine ⟨67201805845417592166876107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44801203896945061444584071 67201805845417592166876107)
    ·
      refine ⟨100802708768126388250314161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67201805845417592166876107 100802708768126388250314161)
      ·
        refine ⟨75602031576094791187735621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100802708768126388250314161 75602031576094791187735621)
        ·
          refine ⟨14175380920517773347700429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75602031576094791187735621 14175380920517773347700429)
          ·
            refine ⟨5315767845194165005387661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14175380920517773347700429 5315767845194165005387661)
            ·
              refine ⟨1993412941947811877020373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5315767845194165005387661 1993412941947811877020373)
              ·
                refine ⟨46720615826901840867665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1993412941947811877020373 46720615826901840867665)
                ·
                  rfl

theorem cell22_1228339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 7].length) (baseStart_1228339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228339 prefixEnd_1228339 := by exact prefixLift 1228339
  have htrace : WordTrace (prefixWord ++ tailWord_1228339) baseStart_1228339 baseEnd_1228339 := by
    simpa [prefixWord, tailWord_1228339, baseEnd_1228339] using wordTrace_append hprefix tailTrace_1228339
  have hstable : (prefixWord ++ tailWord_1228339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228339).length < 2 ^ (prefixWord ++ tailWord_1228339).sum := by decide
  have hdescent : baseEnd_1228339 < baseStart_1228339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228388 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_1228388 : Nat := 118140960795 + 1228388 * 2 ^ 59
def prefixEnd_1228388 : Nat := 4983230072969 + 3 ^ 40 * 1228388 * 2
def baseEnd_1228388 : Nat := 420502316143496773333835

theorem tailTrace_1228388 : CollatzResearch.WordTrace tailWord_1228388 prefixEnd_1228388 420502316143496773333835 := by
  unfold tailWord_1228388
  simp only [CollatzResearch.WordTrace]
  refine ⟨22401495536883771406558909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29868660715845028542078545 22401495536883771406558909)
  ·
    refine ⟨8400560826331414277459591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22401495536883771406558909 8400560826331414277459591)
    ·
      refine ⟨12600841239497121416189387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8400560826331414277459591 12600841239497121416189387)
      ·
        refine ⟨18901261859245682124284081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12600841239497121416189387 18901261859245682124284081)
        ·
          refine ⟨14175946394434261593213061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18901261859245682124284081 14175946394434261593213061)
          ·
            refine ⟨2657989948956424048727449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14175946394434261593213061 2657989948956424048727449)
            ·
              refine ⟨1993492461717318036545587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2657989948956424048727449 1993492461717318036545587)
              ·
                refine ⟨2990238692575977054818381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993492461717318036545587 2990238692575977054818381)
                ·
                  refine ⟨1121339509715991395556893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2990238692575977054818381 1121339509715991395556893)
                  ·
                    refine ⟨420502316143496773333835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121339509715991395556893 420502316143496773333835)
                    ·
                      rfl

theorem cell22_1228388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_1228388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228388 prefixEnd_1228388 := by exact prefixLift 1228388
  have htrace : WordTrace (prefixWord ++ tailWord_1228388) baseStart_1228388 baseEnd_1228388 := by
    simpa [prefixWord, tailWord_1228388, baseEnd_1228388] using wordTrace_append hprefix tailTrace_1228388
  have hstable : (prefixWord ++ tailWord_1228388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228388).length < 2 ^ (prefixWord ++ tailWord_1228388).sum := by decide
  have hdescent : baseEnd_1228388 < baseStart_1228388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228478 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1228478 : Nat := 118140960795 + 1228478 * 2 ^ 59
def prefixEnd_1228478 : Nat := 4983230072969 + 3 ^ 40 * 1228478 * 2
def baseEnd_1228478 : Nat := 420533124982766538583559

theorem tailTrace_1228478 : CollatzResearch.WordTrace tailWord_1228478 prefixEnd_1228478 420533124982766538583559 := by
  unfold tailWord_1228478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600784205430186022986761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29870849095627658789262725 5600784205430186022986761)
  ·
    refine ⟨4200588154072639517240071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5600784205430186022986761 4200588154072639517240071)
    ·
      refine ⟨6300882231108959275860107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4200588154072639517240071 6300882231108959275860107)
      ·
        refine ⟨9451323346663438913790161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6300882231108959275860107 9451323346663438913790161)
        ·
          refine ⟨7088492509997579185342621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9451323346663438913790161 7088492509997579185342621)
          ·
            refine ⟨2658184691249092194503483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7088492509997579185342621 2658184691249092194503483)
            ·
              refine ⟨3987277036873638291755225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658184691249092194503483 3987277036873638291755225)
              ·
                refine ⟨2990457777655228718816419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987277036873638291755225 2990457777655228718816419)
                ·
                  refine ⟨4485686666482843078224629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2990457777655228718816419 4485686666482843078224629)
                  ·
                    refine ⟨420533124982766538583559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4485686666482843078224629 420533124982766538583559)
                    ·
                      rfl

theorem cell22_1228478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1228478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228478 prefixEnd_1228478 := by exact prefixLift 1228478
  have htrace : WordTrace (prefixWord ++ tailWord_1228478) baseStart_1228478 baseEnd_1228478 := by
    simpa [prefixWord, tailWord_1228478, baseEnd_1228478] using wordTrace_append hprefix tailTrace_1228478
  have hstable : (prefixWord ++ tailWord_1228478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228478).length < 2 ^ (prefixWord ++ tailWord_1228478).sum := by decide
  have hdescent : baseEnd_1228478 < baseStart_1228478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228570 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_1228570 : Nat := 118140960795 + 1228570 * 2 ^ 59
def prefixEnd_1228570 : Nat := 4983230072969 + 3 ^ 40 * 1228570 * 2
def baseEnd_1228570 : Nat := 140188206154302988427759

theorem tailTrace_1228570 : CollatzResearch.WordTrace tailWord_1228570 prefixEnd_1228570 140188206154302988427759 := by
  unfold tailWord_1228570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11202407289777046974060791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29873086106072125264162109 11202407289777046974060791)
  ·
    refine ⟨16803610934665570461091187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11202407289777046974060791 16803610934665570461091187)
    ·
      refine ⟨25205416401998355691636781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16803610934665570461091187 25205416401998355691636781)
      ·
        refine ⟨9452031150749383384363793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25205416401998355691636781 9452031150749383384363793)
        ·
          refine ⟨7089023363062037538272845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9452031150749383384363793 7089023363062037538272845)
          ·
            refine ⟨2658383761148264076852317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7089023363062037538272845 2658383761148264076852317)
            ·
              refine ⟨996893910430599028819619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2658383761148264076852317 996893910430599028819619)
              ·
                refine ⟨1495340865645898543229429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996893910430599028819619 1495340865645898543229429)
                ·
                  refine ⟨140188206154302988427759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1495340865645898543229429 140188206154302988427759)
                  ·
                    rfl

theorem cell22_1228570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_1228570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228570 prefixEnd_1228570 := by exact prefixLift 1228570
  have htrace : WordTrace (prefixWord ++ tailWord_1228570) baseStart_1228570 baseEnd_1228570 := by
    simpa [prefixWord, tailWord_1228570, baseEnd_1228570] using wordTrace_append hprefix tailTrace_1228570
  have hstable : (prefixWord ++ tailWord_1228570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228570).length < 2 ^ (prefixWord ++ tailWord_1228570).sum := by decide
  have hdescent : baseEnd_1228570 < baseStart_1228570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228613 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_1228613 : Nat := 118140960795 + 1228613 * 2 ^ 59
def prefixEnd_1228613 : Nat := 4983230072969 + 3 ^ 40 * 1228613 * 2
def baseEnd_1228613 : Nat := 420579338241671186458145

theorem tailTrace_1228613 : CollatzResearch.WordTrace tailWord_1228613 prefixEnd_1228613 420579338241671186458145 := by
  unfold tailWord_1228613
  simp only [CollatzResearch.WordTrace]
  refine ⟨44811197497952406240058493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29874131665301604160038995 44811197497952406240058493)
  ·
    refine ⟨16804199061732152340021935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44811197497952406240058493 16804199061732152340021935)
    ·
      refine ⟨25206298592598228510032903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16804199061732152340021935 25206298592598228510032903)
      ·
        refine ⟨37809447888897342765049355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25206298592598228510032903 37809447888897342765049355)
        ·
          refine ⟨56714171833346014147574033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37809447888897342765049355 56714171833346014147574033)
          ·
            refine ⟨42535628875009510610680525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56714171833346014147574033 42535628875009510610680525)
            ·
              refine ⟨15950860828128566479005197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42535628875009510610680525 15950860828128566479005197)
              ·
                refine ⟨5981572810548212429626949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15950860828128566479005197 5981572810548212429626949)
                ·
                  refine ⟨1121544901977789830555053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5981572810548212429626949 1121544901977789830555053)
                  ·
                    refine ⟨420579338241671186458145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121544901977789830555053 420579338241671186458145)
                    ·
                      rfl

theorem cell22_1228613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_1228613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228613 prefixEnd_1228613 := by exact prefixLift 1228613
  have htrace : WordTrace (prefixWord ++ tailWord_1228613) baseStart_1228613 baseEnd_1228613 := by
    simpa [prefixWord, tailWord_1228613, baseEnd_1228613] using wordTrace_append hprefix tailTrace_1228613
  have hstable : (prefixWord ++ tailWord_1228613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228613).length < 2 ^ (prefixWord ++ tailWord_1228613).sum := by decide
  have hdescent : baseEnd_1228613 < baseStart_1228613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228692 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1228692 : Nat := 118140960795 + 1228692 * 2 ^ 59
def prefixEnd_1228692 : Nat := 4983230072969 + 3 ^ 40 * 1228692 * 2
def baseEnd_1228692 : Nat := 420606381556141313732903

theorem tailTrace_1228692 : CollatzResearch.WordTrace tailWord_1228692 prefixEnd_1228692 420606381556141313732903 := by
  unfold tailWord_1228692
  simp only [CollatzResearch.WordTrace]
  refine ⟨22407039432333101366092165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29876052576444135154789553 22407039432333101366092165)
  ·
    refine ⟨4201319893562456506142281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22407039432333101366092165 4201319893562456506142281)
    ·
      refine ⟨3150989920171842379606711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4201319893562456506142281 3150989920171842379606711)
      ·
        refine ⟨4726484880257763569410067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150989920171842379606711 4726484880257763569410067)
        ·
          refine ⟨7089727320386645354115101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726484880257763569410067 7089727320386645354115101)
          ·
            refine ⟨2658647745144992007793163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7089727320386645354115101 2658647745144992007793163)
            ·
              refine ⟨3987971617717488011689745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2658647745144992007793163 3987971617717488011689745)
              ·
                refine ⟨2990978713288116008767309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3987971617717488011689745 2990978713288116008767309)
                ·
                  refine ⟨1121617017483043503287741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2990978713288116008767309 1121617017483043503287741)
                  ·
                    refine ⟨420606381556141313732903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121617017483043503287741 420606381556141313732903)
                    ·
                      rfl

theorem cell22_1228692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1228692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228692 prefixEnd_1228692 := by exact prefixLift 1228692
  have htrace : WordTrace (prefixWord ++ tailWord_1228692) baseStart_1228692 baseEnd_1228692 := by
    simpa [prefixWord, tailWord_1228692, baseEnd_1228692] using wordTrace_append hprefix tailTrace_1228692
  have hstable : (prefixWord ++ tailWord_1228692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228692).length < 2 ^ (prefixWord ++ tailWord_1228692).sum := by decide
  have hdescent : baseEnd_1228692 < baseStart_1228692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228767 : List Nat := [1, 1, 2, 3, 4, 1, 3, 3, 4]
def baseStart_1228767 : Nat := 118140960795 + 1228767 * 2 ^ 59
def prefixEnd_1228767 : Nat := 4983230072969 + 3 ^ 40 * 1228767 * 2
def baseEnd_1228767 : Nat := 140210685196288706035891

theorem tailTrace_1228767 : CollatzResearch.WordTrace tailWord_1228767 prefixEnd_1228767 140210685196288706035891 := by
  unfold tailWord_1228767
  simp only [CollatzResearch.WordTrace]
  refine ⟨44816814339394490541164555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29877876226262993694109703 44816814339394490541164555)
  ·
    refine ⟨67225221509091735811746833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44816814339394490541164555 67225221509091735811746833)
    ·
      refine ⟨50418916131818801858810125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67225221509091735811746833 50418916131818801858810125)
      ·
        refine ⟨18907093549432050697053797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50418916131818801858810125 18907093549432050697053797)
        ·
          refine ⟨3545080040518509505697587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18907093549432050697053797 3545080040518509505697587)
          ·
            refine ⟨5317620060777764258546381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545080040518509505697587 5317620060777764258546381)
            ·
              refine ⟨1994107522791661596954893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5317620060777764258546381 1994107522791661596954893)
              ·
                refine ⟨747790321046873098858085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1994107522791661596954893 747790321046873098858085)
                ·
                  refine ⟨140210685196288706035891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 747790321046873098858085 140210685196288706035891)
                  ·
                    rfl

theorem cell22_1228767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 4].length) (baseStart_1228767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228767 prefixEnd_1228767 := by exact prefixLift 1228767
  have htrace : WordTrace (prefixWord ++ tailWord_1228767) baseStart_1228767 baseEnd_1228767 := by
    simpa [prefixWord, tailWord_1228767, baseEnd_1228767] using wordTrace_append hprefix tailTrace_1228767
  have hstable : (prefixWord ++ tailWord_1228767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228767).length < 2 ^ (prefixWord ++ tailWord_1228767).sum := by decide
  have hdescent : baseEnd_1228767 < baseStart_1228767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228782 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1228782 : Nat := 118140960795 + 1228782 * 2 ^ 59
def prefixEnd_1228782 : Nat := 4983230072969 + 3 ^ 40 * 1228782 * 2
def baseEnd_1228782 : Nat := 420637190395411078982627

theorem tailTrace_1228782 : CollatzResearch.WordTrace tailWord_1228782 prefixEnd_1228782 420637190395411078982627 := by
  unfold tailWord_1228782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5602170179292518512870075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29878240956226765401973733 5602170179292518512870075)
  ·
    refine ⟨8403255268938777769305113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5602170179292518512870075 8403255268938777769305113)
    ·
      refine ⟨6302441451704083326978835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8403255268938777769305113 6302441451704083326978835)
      ·
        refine ⟨9453662177556124990468253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6302441451704083326978835 9453662177556124990468253)
        ·
          refine ⟨3545123316583546871425595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9453662177556124990468253 3545123316583546871425595)
          ·
            refine ⟨5317684974875320307138393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3545123316583546871425595 5317684974875320307138393)
            ·
              refine ⟨3988263731156490230353795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5317684974875320307138393 3988263731156490230353795)
              ·
                refine ⟨5982395596734735345530693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988263731156490230353795 5982395596734735345530693)
                ·
                  refine ⟨1121699174387762877287005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5982395596734735345530693 1121699174387762877287005)
                  ·
                    refine ⟨420637190395411078982627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121699174387762877287005 420637190395411078982627)
                    ·
                      rfl

theorem cell22_1228782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1228782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228782 prefixEnd_1228782 := by exact prefixLift 1228782
  have htrace : WordTrace (prefixWord ++ tailWord_1228782) baseStart_1228782 baseEnd_1228782 := by
    simpa [prefixWord, tailWord_1228782, baseEnd_1228782] using wordTrace_append hprefix tailTrace_1228782
  have hstable : (prefixWord ++ tailWord_1228782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228782).length < 2 ^ (prefixWord ++ tailWord_1228782).sum := by decide
  have hdescent : baseEnd_1228782 < baseStart_1228782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228900 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_1228900 : Nat := 118140960795 + 1228900 * 2 ^ 59
def prefixEnd_1228900 : Nat := 4983230072969 + 3 ^ 40 * 1228900 * 2
def baseEnd_1228900 : Nat := 420677584206898104532265

theorem tailTrace_1228900 : CollatzResearch.WordTrace tailWord_1228900 prefixEnd_1228900 420677584206898104532265 := by
  unfold tailWord_1228900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22410832623956327127878077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29881110165275102837170769 22410832623956327127878077)
  ·
    refine ⟨8404062233983622672954279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22410832623956327127878077 8404062233983622672954279)
    ·
      refine ⟨12606093350975434009431419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8404062233983622672954279 12606093350975434009431419)
      ·
        refine ⟨18909140026463151014147129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12606093350975434009431419 18909140026463151014147129)
        ·
          refine ⟨14181855019847363260610347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18909140026463151014147129 14181855019847363260610347)
          ·
            refine ⟨21272782529771044890915521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14181855019847363260610347 21272782529771044890915521)
            ·
              refine ⟨15954586897328283668186641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21272782529771044890915521 15954586897328283668186641)
              ·
                refine ⟨11965940172996212751139981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15954586897328283668186641 11965940172996212751139981)
                ·
                  refine ⟨4487227564873579781677493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11965940172996212751139981 4487227564873579781677493)
                  ·
                    refine ⟨420677584206898104532265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4487227564873579781677493 420677584206898104532265)
                    ·
                      rfl

theorem cell22_1228900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_1228900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228900 prefixEnd_1228900 := by exact prefixLift 1228900
  have htrace : WordTrace (prefixWord ++ tailWord_1228900) baseStart_1228900 baseEnd_1228900 := by
    simpa [prefixWord, tailWord_1228900, baseEnd_1228900] using wordTrace_append hprefix tailTrace_1228900
  have hstable : (prefixWord ++ tailWord_1228900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228900).length < 2 ^ (prefixWord ++ tailWord_1228900).sum := by decide
  have hdescent : baseEnd_1228900 < baseStart_1228900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228932 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1228932 : Nat := 118140960795 + 1228932 * 2 ^ 59
def prefixEnd_1228932 : Nat := 4983230072969 + 3 ^ 40 * 1228932 * 2
def baseEnd_1228932 : Nat := 420688538460860687732167

theorem tailTrace_1228932 : CollatzResearch.WordTrace tailWord_1228932 prefixEnd_1228932 420688538460860687732167 := by
  unfold tailWord_1228932
  simp only [CollatzResearch.WordTrace]
  refine ⟨22411416191898361860460525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29881888255864482480614033 22411416191898361860460525)
  ·
    refine ⟨8404281071961885697672697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22411416191898361860460525 8404281071961885697672697)
    ·
      refine ⟨6303210803971414273254523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8404281071961885697672697 6303210803971414273254523)
      ·
        refine ⟨9454816205957121409881785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6303210803971414273254523 9454816205957121409881785)
        ·
          refine ⟨7091112154467841057411339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9454816205957121409881785 7091112154467841057411339)
          ·
            refine ⟨10636668231701761586117009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7091112154467841057411339 10636668231701761586117009)
            ·
              refine ⟨7977501173776321189587757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10636668231701761586117009 7977501173776321189587757)
              ·
                refine ⟨2991562940166120446095409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7977501173776321189587757 2991562940166120446095409)
                ·
                  refine ⟨2243672205124590334571557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2991562940166120446095409 2243672205124590334571557)
                  ·
                    refine ⟨420688538460860687732167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2243672205124590334571557 420688538460860687732167)
                    ·
                      rfl

theorem cell22_1228932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1228932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228932 prefixEnd_1228932 := by exact prefixLift 1228932
  have htrace : WordTrace (prefixWord ++ tailWord_1228932) baseStart_1228932 baseEnd_1228932 := by
    simpa [prefixWord, tailWord_1228932, baseEnd_1228932] using wordTrace_append hprefix tailTrace_1228932
  have hstable : (prefixWord ++ tailWord_1228932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228932).length < 2 ^ (prefixWord ++ tailWord_1228932).sum := by decide
  have hdescent : baseEnd_1228932 < baseStart_1228932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1228936 : List Nat := [2, 1, 3, 4, 1, 3, 1, 3, 4]
def baseStart_1228936 : Nat := 118140960795 + 1228936 * 2 ^ 59
def prefixEnd_1228936 : Nat := 4983230072969 + 3 ^ 40 * 1228936 * 2
def baseEnd_1228936 : Nat := 140229969247535336877385

theorem tailTrace_1228936 : CollatzResearch.WordTrace tailWord_1228936 prefixEnd_1228936 140229969247535336877385 := by
  unfold tailWord_1228936
  simp only [CollatzResearch.WordTrace]
  refine ⟨22411489137891116202033331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29881985517188154936044441 22411489137891116202033331)
  ·
    refine ⟨33617233706836674303049997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22411489137891116202033331 33617233706836674303049997)
    ·
      refine ⟨12606462640063752863643749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33617233706836674303049997 12606462640063752863643749)
      ·
        refine ⟨2363711745011953661933203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12606462640063752863643749 2363711745011953661933203)
        ·
          refine ⟨3545567617517930492899805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363711745011953661933203 3545567617517930492899805)
          ·
            refine ⟨1329587856569223934837427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3545567617517930492899805 1329587856569223934837427)
            ·
              refine ⟨1994381784853835902256141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329587856569223934837427 1994381784853835902256141)
              ·
                refine ⟨747893169320188463346053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1994381784853835902256141 747893169320188463346053)
                ·
                  refine ⟨140229969247535336877385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 747893169320188463346053 140229969247535336877385)
                  ·
                    rfl

theorem cell22_1228936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 4].length) (baseStart_1228936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1228936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1228936 prefixEnd_1228936 := by exact prefixLift 1228936
  have htrace : WordTrace (prefixWord ++ tailWord_1228936) baseStart_1228936 baseEnd_1228936 := by
    simpa [prefixWord, tailWord_1228936, baseEnd_1228936] using wordTrace_append hprefix tailTrace_1228936
  have hstable : (prefixWord ++ tailWord_1228936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1228936).length < 2 ^ (prefixWord ++ tailWord_1228936).sum := by decide
  have hdescent : baseEnd_1228936 < baseStart_1228936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1228936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229013 : List Nat := [1, 3, 2, 4, 2, 1, 1, 4, 1, 3]
def baseStart_1229013 : Nat := 118140960795 + 1229013 * 2 ^ 59
def prefixEnd_1229013 : Nat := 4983230072969 + 3 ^ 40 * 1229013 * 2
def baseEnd_1229013 : Nat := 420716266416203476456919

theorem tailTrace_1229013 : CollatzResearch.WordTrace tailWord_1229013 prefixEnd_1229013 420716266416203476456919 := by
  unfold tailWord_1229013
  simp only [CollatzResearch.WordTrace]
  refine ⟨44825786696503274554619693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29883857797668849703079795 44825786696503274554619693)
  ·
    refine ⟨16809670011188727957982385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44825786696503274554619693 16809670011188727957982385)
    ·
      refine ⟨12607252508391545968486789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16809670011188727957982385 12607252508391545968486789)
      ·
        refine ⟨2363859845323414869091273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12607252508391545968486789 2363859845323414869091273)
        ·
          refine ⟨1772894883992561151818455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2363859845323414869091273 1772894883992561151818455)
          ·
            refine ⟨2659342325988841727727683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772894883992561151818455 2659342325988841727727683)
            ·
              refine ⟨3989013488983262591591525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2659342325988841727727683 3989013488983262591591525)
              ·
                refine ⟨747940029184361735923411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3989013488983262591591525 747940029184361735923411)
                ·
                  refine ⟨1121910043776542603885117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747940029184361735923411 1121910043776542603885117)
                  ·
                    refine ⟨420716266416203476456919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1121910043776542603885117 420716266416203476456919)
                    ·
                      rfl

theorem cell22_1229013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_1229013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229013 prefixEnd_1229013 := by exact prefixLift 1229013
  have htrace : WordTrace (prefixWord ++ tailWord_1229013) baseStart_1229013 baseEnd_1229013 := by
    simpa [prefixWord, tailWord_1229013, baseEnd_1229013] using wordTrace_append hprefix tailTrace_1229013
  have hstable : (prefixWord ++ tailWord_1229013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229013).length < 2 ^ (prefixWord ++ tailWord_1229013).sum := by decide
  have hdescent : baseEnd_1229013 < baseStart_1229013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229067 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 4, 4]
def baseStart_1229067 : Nat := 118140960795 + 1229067 * 2 ^ 59
def prefixEnd_1229067 : Nat := 4983230072969 + 3 ^ 40 * 1229067 * 2
def baseEnd_1229067 : Nat := 420734751719765335606753

theorem tailTrace_1229067 : CollatzResearch.WordTrace tailWord_1229067 prefixEnd_1229067 420734751719765335606753 := by
  unfold tailWord_1229067
  simp only [CollatzResearch.WordTrace]
  refine ⟨44827756238307641777085455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29885170825538427851390303 44827756238307641777085455)
  ·
    refine ⟨67241634357461462665628183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44827756238307641777085455 67241634357461462665628183)
    ·
      refine ⟨100862451536192193998442275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67241634357461462665628183 100862451536192193998442275)
      ·
        refine ⟨151293677304288290997663413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100862451536192193998442275 151293677304288290997663413)
        ·
          refine ⟨14183782247277027281030945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151293677304288290997663413 14183782247277027281030945)
          ·
            refine ⟨10637836685457770460773209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14183782247277027281030945 10637836685457770460773209)
            ·
              refine ⟨7978377514093327845579907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10637836685457770460773209 7978377514093327845579907)
              ·
                refine ⟨11967566271139991768369861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7978377514093327845579907 11967566271139991768369861)
                ·
                  refine ⟨2243918675838748456569349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11967566271139991768369861 2243918675838748456569349)
                  ·
                    refine ⟨420734751719765335606753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2243918675838748456569349 420734751719765335606753)
                    ·
                      rfl

theorem cell22_1229067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 4].length) (baseStart_1229067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229067 prefixEnd_1229067 := by exact prefixLift 1229067
  have htrace : WordTrace (prefixWord ++ tailWord_1229067) baseStart_1229067 baseEnd_1229067 := by
    simpa [prefixWord, tailWord_1229067, baseEnd_1229067] using wordTrace_append hprefix tailTrace_1229067
  have hstable : (prefixWord ++ tailWord_1229067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229067).length < 2 ^ (prefixWord ++ tailWord_1229067).sum := by decide
  have hdescent : baseEnd_1229067 < baseStart_1229067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229127 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 7]
def baseStart_1229127 : Nat := 118140960795 + 1229127 * 2 ^ 59
def prefixEnd_1229127 : Nat := 4983230072969 + 3 ^ 40 * 1229127 * 2
def baseEnd_1229127 : Nat := 140251763648648393035523

theorem tailTrace_1229127 : CollatzResearch.WordTrace tailWord_1229127 prefixEnd_1229127 140251763648648393035523 := by
  unfold tailWord_1229127
  simp only [CollatzResearch.WordTrace]
  refine ⟨44829944618090272024269635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29886629745393514682846423 44829944618090272024269635)
  ·
    refine ⟨67244916927135408036404453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44829944618090272024269635 67244916927135408036404453)
    ·
      refine ⟨12608421923837889006825835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67244916927135408036404453 12608421923837889006825835)
      ·
        refine ⟨18912632885756833510238753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12608421923837889006825835 18912632885756833510238753)
        ·
          refine ⟨14184474664317625132679065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18912632885756833510238753 14184474664317625132679065)
          ·
            refine ⟨10638355998238218849509299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14184474664317625132679065 10638355998238218849509299)
            ·
              refine ⟨15957533997357328274263949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10638355998238218849509299 15957533997357328274263949)
              ·
                refine ⟨5984075249008998102848981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15957533997357328274263949 5984075249008998102848981)
                ·
                  refine ⟨140251763648648393035523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5984075249008998102848981 140251763648648393035523)
                  ·
                    rfl

theorem cell22_1229127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 7].length) (baseStart_1229127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229127 prefixEnd_1229127 := by exact prefixLift 1229127
  have htrace : WordTrace (prefixWord ++ tailWord_1229127) baseStart_1229127 baseEnd_1229127 := by
    simpa [prefixWord, tailWord_1229127, baseEnd_1229127] using wordTrace_append hprefix tailTrace_1229127
  have hstable : (prefixWord ++ tailWord_1229127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229127).length < 2 ^ (prefixWord ++ tailWord_1229127).sum := by decide
  have hdescent : baseEnd_1229127 < baseStart_1229127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229219 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 1, 6]
def baseStart_1229219 : Nat := 118140960795 + 1229219 * 2 ^ 59
def prefixEnd_1229219 : Nat := 4983230072969 + 3 ^ 40 * 1229219 * 2
def baseEnd_1229219 : Nat := 420786784426087605806287

theorem tailTrace_1229219 : CollatzResearch.WordTrace tailWord_1229219 prefixEnd_1229219 420786784426087605806287 := by
  unfold tailWord_1229219
  simp only [CollatzResearch.WordTrace]
  refine ⟨44833300133756971736618711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29888866755837981157745807 44833300133756971736618711)
  ·
    refine ⟨67249950200635457604928067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44833300133756971736618711 67249950200635457604928067)
    ·
      refine ⟨100874925300953186407392101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67249950200635457604928067 100874925300953186407392101)
      ·
        refine ⟨18914048493928722451386019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100874925300953186407392101 18914048493928722451386019)
        ·
          refine ⟨28371072740893083677079029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18914048493928722451386019 28371072740893083677079029)
          ·
            refine ⟨2659788069458726594726159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28371072740893083677079029 2659788069458726594726159)
            ·
              refine ⟨3989682104188089892089239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2659788069458726594726159 3989682104188089892089239)
              ·
                refine ⟨5984523156282134838133859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3989682104188089892089239 5984523156282134838133859)
                ·
                  refine ⟨8976784734423202257200789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5984523156282134838133859 8976784734423202257200789)
                  ·
                    refine ⟨420786784426087605806287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8976784734423202257200789 420786784426087605806287)
                    ·
                      rfl

theorem cell22_1229219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 6].length) (baseStart_1229219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229219 prefixEnd_1229219 := by exact prefixLift 1229219
  have htrace : WordTrace (prefixWord ++ tailWord_1229219) baseStart_1229219 baseEnd_1229219 := by
    simpa [prefixWord, tailWord_1229219, baseEnd_1229219] using wordTrace_append hprefix tailTrace_1229219
  have hstable : (prefixWord ++ tailWord_1229219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229219).length < 2 ^ (prefixWord ++ tailWord_1229219).sum := by decide
  have hdescent : baseEnd_1229219 < baseStart_1229219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229223 : List Nat := [1, 1, 6, 1, 1, 3, 2, 3, 4]
def baseStart_1229223 : Nat := 118140960795 + 1229223 * 2 ^ 59
def prefixEnd_1229223 : Nat := 4983230072969 + 3 ^ 40 * 1229223 * 2
def baseEnd_1229223 : Nat := 140262717902610976235425

theorem tailTrace_1229223 : CollatzResearch.WordTrace tailWord_1229223 prefixEnd_1229223 140262717902610976235425 := by
  unfold tailWord_1229223
  simp only [CollatzResearch.WordTrace]
  refine ⟨44833446025742480419764323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29888964017161653613176215 44833446025742480419764323)
  ·
    refine ⟨67250169038613720629646485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44833446025742480419764323 67250169038613720629646485)
    ·
      refine ⟨3152351673685018154514679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67250169038613720629646485 3152351673685018154514679)
      ·
        refine ⟨4728527510527527231772019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3152351673685018154514679 4728527510527527231772019)
        ·
          refine ⟨7092791265791290847658029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4728527510527527231772019 7092791265791290847658029)
          ·
            refine ⟨2659796724671734067871761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7092791265791290847658029 2659796724671734067871761)
            ·
              refine ⟨1994847543503800550903821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2659796724671734067871761 1994847543503800550903821)
              ·
                refine ⟨748067828813925206588933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1994847543503800550903821 748067828813925206588933)
                ·
                  refine ⟨140262717902610976235425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748067828813925206588933 140262717902610976235425)
                  ·
                    rfl

theorem cell22_1229223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 4].length) (baseStart_1229223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229223 prefixEnd_1229223 := by exact prefixLift 1229223
  have htrace : WordTrace (prefixWord ++ tailWord_1229223) baseStart_1229223 baseEnd_1229223 := by
    simpa [prefixWord, tailWord_1229223, baseEnd_1229223] using wordTrace_append hprefix tailTrace_1229223
  have hstable : (prefixWord ++ tailWord_1229223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229223).length < 2 ^ (prefixWord ++ tailWord_1229223).sum := by decide
  have hdescent : baseEnd_1229223 < baseStart_1229223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229268 : List Nat := [2, 4, 1, 2, 2, 3, 2, 6]
def baseStart_1229268 : Nat := 118140960795 + 1229268 * 2 ^ 59
def prefixEnd_1229268 : Nat := 4983230072969 + 3 ^ 40 * 1229268 * 2
def baseEnd_1229268 : Nat := 46755950903051979036793

theorem tailTrace_1229268 : CollatzResearch.WordTrace tailWord_1229268 prefixEnd_1229268 46755950903051979036793 := by
  unfold tailWord_1229268
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417543655289726552576229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29890058207052968736768305 22417543655289726552576229)
  ·
    refine ⟨4203289435366823728608043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22417543655289726552576229 4203289435366823728608043)
    ·
      refine ⟨6304934153050235592912065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4203289435366823728608043 6304934153050235592912065)
      ·
        refine ⟨4728700614787676694684049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6304934153050235592912065 4728700614787676694684049)
        ·
          refine ⟨3546525461090757521013037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4728700614787676694684049 3546525461090757521013037)
          ·
            refine ⟨1329947047909034070379889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3546525461090757521013037 1329947047909034070379889)
            ·
              refine ⟨997460285931775552784917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1329947047909034070379889 997460285931775552784917)
              ·
                refine ⟨46755950903051979036793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 997460285931775552784917 46755950903051979036793)
                ·
                  rfl

theorem cell22_1229268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 6].length) (baseStart_1229268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229268 prefixEnd_1229268 := by exact prefixLift 1229268
  have htrace : WordTrace (prefixWord ++ tailWord_1229268) baseStart_1229268 baseEnd_1229268 := by
    simpa [prefixWord, tailWord_1229268, baseEnd_1229268] using wordTrace_append hprefix tailTrace_1229268
  have hstable : (prefixWord ++ tailWord_1229268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229268).length < 2 ^ (prefixWord ++ tailWord_1229268).sum := by decide
  have hdescent : baseEnd_1229268 < baseStart_1229268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229279 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 7]
def baseStart_1229279 : Nat := 118140960795 + 1229279 * 2 ^ 59
def prefixEnd_1229279 : Nat := 4983230072969 + 3 ^ 40 * 1229279 * 2
def baseEnd_1229279 : Nat := 140269107884089149768701

theorem tailTrace_1229279 : CollatzResearch.WordTrace tailWord_1229279 prefixEnd_1229279 140269107884089149768701 := by
  unfold tailWord_1229279
  simp only [CollatzResearch.WordTrace]
  refine ⟨44835488513539601983802891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29890325675693067989201927 44835488513539601983802891)
  ·
    refine ⟨67253232770309402975704337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44835488513539601983802891 67253232770309402975704337)
    ·
      refine ⟨50439924577732052231778253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67253232770309402975704337 50439924577732052231778253)
      ·
        refine ⟨18914971716649519586916845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50439924577732052231778253 18914971716649519586916845)
        ·
          refine ⟨7093114393743569845093817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18914971716649519586916845 7093114393743569845093817)
          ·
            refine ⟨5319835795307677383820363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7093114393743569845093817 5319835795307677383820363)
            ·
              refine ⟨7979753692961516075730545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5319835795307677383820363 7979753692961516075730545)
              ·
                refine ⟨5984815269721137056797909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7979753692961516075730545 5984815269721137056797909)
                ·
                  refine ⟨140269107884089149768701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5984815269721137056797909 140269107884089149768701)
                  ·
                    rfl

theorem cell22_1229279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 7].length) (baseStart_1229279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229279 prefixEnd_1229279 := by exact prefixLift 1229279
  have htrace : WordTrace (prefixWord ++ tailWord_1229279) baseStart_1229279 baseEnd_1229279 := by
    simpa [prefixWord, tailWord_1229279, baseEnd_1229279] using wordTrace_append hprefix tailTrace_1229279
  have hstable : (prefixWord ++ tailWord_1229279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229279).length < 2 ^ (prefixWord ++ tailWord_1229279).sum := by decide
  have hdescent : baseEnd_1229279 < baseStart_1229279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229313 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 5]
def baseStart_1229313 : Nat := 118140960795 + 1229313 * 2 ^ 59
def prefixEnd_1229313 : Nat := 4983230072969 + 3 ^ 40 * 1229313 * 2
def baseEnd_1229313 : Nat := 140272987515700897985333

theorem tailTrace_1229313 : CollatzResearch.WordTrace tailWord_1229313 prefixEnd_1229313 140272987515700897985333 := by
  unfold tailWord_1229313
  simp only [CollatzResearch.WordTrace]
  refine ⟨44836728595416425790540593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29891152396944283860360395 44836728595416425790540593)
  ·
    refine ⟨33627546446562319342905445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44836728595416425790540593 33627546446562319342905445)
    ·
      refine ⟨6305164958730434876794771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33627546446562319342905445 6305164958730434876794771)
      ·
        refine ⟨9457747438095652315192157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6305164958730434876794771 9457747438095652315192157)
        ·
          refine ⟨3546655289285869618197059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9457747438095652315192157 3546655289285869618197059)
          ·
            refine ⟨5319982933928804427295589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546655289285869618197059 5319982933928804427295589)
            ·
              refine ⟨997496800111650830117923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5319982933928804427295589 997496800111650830117923)
              ·
                refine ⟨1496245200167476245176885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997496800111650830117923 1496245200167476245176885)
                ·
                  refine ⟨140272987515700897985333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1496245200167476245176885 140272987515700897985333)
                  ·
                    rfl

theorem cell22_1229313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 5].length) (baseStart_1229313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229313 prefixEnd_1229313 := by exact prefixLift 1229313
  have htrace : WordTrace (prefixWord ++ tailWord_1229313) baseStart_1229313 baseEnd_1229313 := by
    simpa [prefixWord, tailWord_1229313, baseEnd_1229313] using wordTrace_append hprefix tailTrace_1229313
  have hstable : (prefixWord ++ tailWord_1229313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229313).length < 2 ^ (prefixWord ++ tailWord_1229313).sum := by decide
  have hdescent : baseEnd_1229313 < baseStart_1229313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229351 : List Nat := [1, 1, 7, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1229351 : Nat := 118140960795 + 1229351 * 2 ^ 59
def prefixEnd_1229351 : Nat := 4983230072969 + 3 ^ 40 * 1229351 * 2
def baseEnd_1229351 : Nat := 420831970723683261505883

theorem tailTrace_1229351 : CollatzResearch.WordTrace tailWord_1229351 prefixEnd_1229351 420831970723683261505883 := by
  unfold tailWord_1229351
  simp only [CollatzResearch.WordTrace]
  refine ⟨44838114569278758280423907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29892076379519172186949271 44838114569278758280423907)
  ·
    refine ⟨67257171853918137420635861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44838114569278758280423907 67257171853918137420635861)
    ·
      refine ⟨1576339965326206345796153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 67257171853918137420635861 1576339965326206345796153)
      ·
        refine ⟨1182254973994654759347115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1576339965326206345796153 1182254973994654759347115)
        ·
          refine ⟨1773382460991982139020673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182254973994654759347115 1773382460991982139020673)
          ·
            refine ⟨1330036845743986604265505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1773382460991982139020673 1330036845743986604265505)
            ·
              refine ⟨997527634307989953199129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330036845743986604265505 997527634307989953199129)
              ·
                refine ⟨748145725730992464899347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997527634307989953199129 748145725730992464899347)
                ·
                  refine ⟨1122218588596488697349021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748145725730992464899347 1122218588596488697349021)
                  ·
                    refine ⟨420831970723683261505883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1122218588596488697349021 420831970723683261505883)
                    ·
                      rfl

theorem cell22_1229351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1229351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229351 prefixEnd_1229351 := by exact prefixLift 1229351
  have htrace : WordTrace (prefixWord ++ tailWord_1229351) baseStart_1229351 baseEnd_1229351 := by
    simpa [prefixWord, tailWord_1229351, baseEnd_1229351] using wordTrace_append hprefix tailTrace_1229351
  have hstable : (prefixWord ++ tailWord_1229351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229351).length < 2 ^ (prefixWord ++ tailWord_1229351).sum := by decide
  have hdescent : baseEnd_1229351 < baseStart_1229351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229356 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_1229356 : Nat := 118140960795 + 1229356 * 2 ^ 59
def prefixEnd_1229356 : Nat := 4983230072969 + 3 ^ 40 * 1229356 * 2
def baseEnd_1229356 : Nat := 420833682325864915130867

theorem tailTrace_1229356 : CollatzResearch.WordTrace tailWord_1229356 prefixEnd_1229356 420833682325864915130867 := by
  unfold tailWord_1229356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22419148467130322067177961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29892197956173762756237281 22419148467130322067177961)
  ·
    refine ⟨16814361350347741550383471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22419148467130322067177961 16814361350347741550383471)
    ·
      refine ⟨25221542025521612325575207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16814361350347741550383471 25221542025521612325575207)
      ·
        refine ⟨37832313038282418488362811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25221542025521612325575207 37832313038282418488362811)
        ·
          refine ⟨56748469557423627732544217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37832313038282418488362811 56748469557423627732544217)
          ·
            refine ⟨42561352168067720799408163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56748469557423627732544217 42561352168067720799408163)
            ·
              refine ⟨63842028252101581199112245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42561352168067720799408163 63842028252101581199112245)
              ·
                refine ⟨5985190148634523237416773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63842028252101581199112245 5985190148634523237416773)
                ·
                  refine ⟨1122223152868973107015645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5985190148634523237416773 1122223152868973107015645)
                  ·
                    refine ⟨420833682325864915130867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1122223152868973107015645 420833682325864915130867)
                    ·
                      rfl

theorem cell22_1229356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_1229356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229356 prefixEnd_1229356 := by exact prefixLift 1229356
  have htrace : WordTrace (prefixWord ++ tailWord_1229356) baseStart_1229356 baseEnd_1229356 := by
    simpa [prefixWord, tailWord_1229356, baseEnd_1229356] using wordTrace_append hprefix tailTrace_1229356
  have hstable : (prefixWord ++ tailWord_1229356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229356).length < 2 ^ (prefixWord ++ tailWord_1229356).sum := by decide
  have hdescent : baseEnd_1229356 < baseStart_1229356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229373 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_1229373 : Nat := 118140960795 + 1229373 * 2 ^ 59
def prefixEnd_1229373 : Nat := 4983230072969 + 3 ^ 40 * 1229373 * 2
def baseEnd_1229373 : Nat := 420839501773282537455815

theorem tailTrace_1229373 : CollatzResearch.WordTrace tailWord_1229373 prefixEnd_1229373 420839501773282537455815 := by
  unfold tailWord_1229373
  simp only [CollatzResearch.WordTrace]
  refine ⟨44838916975199056037724773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29892611316799370691816515 44838916975199056037724773)
  ·
    refine ⟨8407296932849823007073395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44838916975199056037724773 8407296932849823007073395)
    ·
      refine ⟨12610945399274734510610093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8407296932849823007073395 12610945399274734510610093)
      ·
        refine ⟨4729104524728025441478785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12610945399274734510610093 4729104524728025441478785)
        ·
          refine ⟨3546828393546019081109089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4729104524728025441478785 3546828393546019081109089)
          ·
            refine ⟨2660121295159514310831817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3546828393546019081109089 2660121295159514310831817)
            ·
              refine ⟨1995090971369635733123863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2660121295159514310831817 1995090971369635733123863)
              ·
                refine ⟨2992636457054453599685795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995090971369635733123863 2992636457054453599685795)
                ·
                  refine ⟨4488954685581680399528693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2992636457054453599685795 4488954685581680399528693)
                  ·
                    refine ⟨420839501773282537455815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4488954685581680399528693 420839501773282537455815)
                    ·
                      rfl

theorem cell22_1229373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_1229373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229373 prefixEnd_1229373 := by exact prefixLift 1229373
  have htrace : WordTrace (prefixWord ++ tailWord_1229373) baseStart_1229373 baseEnd_1229373 := by
    simpa [prefixWord, tailWord_1229373, baseEnd_1229373] using wordTrace_append hprefix tailTrace_1229373
  have hstable : (prefixWord ++ tailWord_1229373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229373).length < 2 ^ (prefixWord ++ tailWord_1229373).sum := by decide
  have hdescent : baseEnd_1229373 < baseStart_1229373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229431 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 5]
def baseStart_1229431 : Nat := 118140960795 + 1229431 * 2 ^ 59
def prefixEnd_1229431 : Nat := 4983230072969 + 3 ^ 40 * 1229431 * 2
def baseEnd_1229431 : Nat := 140286452119529906501879

theorem tailTrace_1229431 : CollatzResearch.WordTrace tailWord_1229431 prefixEnd_1229431 140286452119529906501879 := by
  unfold tailWord_1229431
  simp only [CollatzResearch.WordTrace]
  refine ⟨44841032408988931943336147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29894021605992621295557431 44841032408988931943336147)
  ·
    refine ⟨67261548613483397915004221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44841032408988931943336147 67261548613483397915004221)
    ·
      refine ⟨25223080730056274218126583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67261548613483397915004221 25223080730056274218126583)
      ·
        refine ⟨37834621095084411327189875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25223080730056274218126583 37834621095084411327189875)
        ·
          refine ⟨56751931642626616990784813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37834621095084411327189875 56751931642626616990784813)
          ·
            refine ⟨21281974365984981371544305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56751931642626616990784813 21281974365984981371544305)
            ·
              refine ⟨15961480774488736028658229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21281974365984981371544305 15961480774488736028658229)
              ·
                refine ⟨1496388822608319002686709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15961480774488736028658229 1496388822608319002686709)
                ·
                  refine ⟨140286452119529906501879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1496388822608319002686709 140286452119529906501879)
                  ·
                    rfl

theorem cell22_1229431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 5].length) (baseStart_1229431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229431 prefixEnd_1229431 := by exact prefixLift 1229431
  have htrace : WordTrace (prefixWord ++ tailWord_1229431) baseStart_1229431 baseEnd_1229431 := by
    simpa [prefixWord, tailWord_1229431, baseEnd_1229431] using wordTrace_append hprefix tailTrace_1229431
  have hstable : (prefixWord ++ tailWord_1229431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229431).length < 2 ^ (prefixWord ++ tailWord_1229431).sum := by decide
  have hdescent : baseEnd_1229431 < baseStart_1229431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229461 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1229461 : Nat := 118140960795 + 1229461 * 2 ^ 59
def prefixEnd_1229461 : Nat := 4983230072969 + 3 ^ 40 * 1229461 * 2
def baseEnd_1229461 : Nat := 420869625971679641255545

theorem tailTrace_1229461 : CollatzResearch.WordTrace tailWord_1229461 prefixEnd_1229461 420869625971679641255545 := by
  unfold tailWord_1229461
  simp only [CollatzResearch.WordTrace]
  refine ⟨44842126598880247066928237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29894751065920164711285491 44842126598880247066928237)
  ·
    refine ⟨16815797474580092650098089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44842126598880247066928237 16815797474580092650098089)
    ·
      refine ⟨12611848105935069487573567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16815797474580092650098089 12611848105935069487573567)
      ·
        refine ⟨18917772158902604231360351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12611848105935069487573567 18917772158902604231360351)
        ·
          refine ⟨28376658238353906347040527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18917772158902604231360351 28376658238353906347040527)
          ·
            refine ⟨42564987357530859520560791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28376658238353906347040527 42564987357530859520560791)
            ·
              refine ⟨63847481036296289280841187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42564987357530859520560791 63847481036296289280841187)
              ·
                refine ⟨95771221554444433921261781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63847481036296289280841187 95771221554444433921261781)
                ·
                  refine ⟨2244638005182291420029573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 95771221554444433921261781 2244638005182291420029573)
                  ·
                    refine ⟨420869625971679641255545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2244638005182291420029573 420869625971679641255545)
                    ·
                      rfl

theorem cell22_1229461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1229461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229461 prefixEnd_1229461 := by exact prefixLift 1229461
  have htrace : WordTrace (prefixWord ++ tailWord_1229461) baseStart_1229461 baseEnd_1229461 := by
    simpa [prefixWord, tailWord_1229461, baseEnd_1229461] using wordTrace_append hprefix tailTrace_1229461
  have hstable : (prefixWord ++ tailWord_1229461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229461).length < 2 ^ (prefixWord ++ tailWord_1229461).sum := by decide
  have hdescent : baseEnd_1229461 < baseStart_1229461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229482 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_1229482 : Nat := 118140960795 + 1229482 * 2 ^ 59
def prefixEnd_1229482 : Nat := 4983230072969 + 3 ^ 40 * 1229482 * 2
def baseEnd_1229482 : Nat := 140292271566947528826827

theorem tailTrace_1229482 : CollatzResearch.WordTrace tailWord_1229482 prefixEnd_1229482 140292271566947528826827 := by
  unfold tailWord_1229482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11210723132951041913360675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29895261687869445102295133 11210723132951041913360675)
  ·
    refine ⟨16816084699426562870041013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11210723132951041913360675 16816084699426562870041013)
    ·
      refine ⟨1576507940571240269066345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16816084699426562870041013 1576507940571240269066345)
      ·
        refine ⟨1182380955428430201799759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1576507940571240269066345 1182380955428430201799759)
        ·
          refine ⟨1773571433142645302699639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182380955428430201799759 1773571433142645302699639)
          ·
            refine ⟨2660357149713967954049459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773571433142645302699639 2660357149713967954049459)
            ·
              refine ⟨3990535724570951931074189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660357149713967954049459 3990535724570951931074189)
              ·
                refine ⟨1496450896714106974152821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3990535724570951931074189 1496450896714106974152821)
                ·
                  refine ⟨140292271566947528826827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1496450896714106974152821 140292271566947528826827)
                  ·
                    rfl

theorem cell22_1229482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_1229482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229482 prefixEnd_1229482 := by exact prefixLift 1229482
  have htrace : WordTrace (prefixWord ++ tailWord_1229482) baseStart_1229482 baseEnd_1229482 := by
    simpa [prefixWord, tailWord_1229482, baseEnd_1229482] using wordTrace_append hprefix tailTrace_1229482
  have hstable : (prefixWord ++ tailWord_1229482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229482).length < 2 ^ (prefixWord ++ tailWord_1229482).sum := by decide
  have hdescent : baseEnd_1229482 < baseStart_1229482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229508 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1229508 : Nat := 118140960795 + 1229508 * 2 ^ 59
def prefixEnd_1229508 : Nat := 4983230072969 + 3 ^ 40 * 1229508 * 2
def baseEnd_1229508 : Nat := 420885715032187185330401

theorem tailTrace_1229508 : CollatzResearch.WordTrace tailWord_1229508 prefixEnd_1229508 420885715032187185330401 := by
  unfold tailWord_1229508
  simp only [CollatzResearch.WordTrace]
  refine ⟨22421920414854987046944589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29895893886473316062592785 22421920414854987046944589)
  ·
    refine ⟨8408220155570620142604221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22421920414854987046944589 8408220155570620142604221)
    ·
      refine ⟨3153082558338982553476583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8408220155570620142604221 3153082558338982553476583)
      ·
        refine ⟨4729623837508473830214875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153082558338982553476583 4729623837508473830214875)
        ·
          refine ⟨7094435756262710745322313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4729623837508473830214875 7094435756262710745322313)
          ·
            refine ⟨5320826817197033058991735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7094435756262710745322313 5320826817197033058991735)
            ·
              refine ⟨7981240225795549588487603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5320826817197033058991735 7981240225795549588487603)
              ·
                refine ⟨11971860338693324382731405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7981240225795549588487603 11971860338693324382731405)
                ·
                  refine ⟨4489447627009996643524277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11971860338693324382731405 4489447627009996643524277)
                  ·
                    refine ⟨420885715032187185330401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4489447627009996643524277 420885715032187185330401)
                    ·
                      rfl

theorem cell22_1229508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1229508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229508 prefixEnd_1229508 := by exact prefixLift 1229508
  have htrace : WordTrace (prefixWord ++ tailWord_1229508) baseStart_1229508 baseEnd_1229508 := by
    simpa [prefixWord, tailWord_1229508, baseEnd_1229508] using wordTrace_append hprefix tailTrace_1229508
  have hstable : (prefixWord ++ tailWord_1229508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229508).length < 2 ^ (prefixWord ++ tailWord_1229508).sum := by decide
  have hdescent : baseEnd_1229508 < baseStart_1229508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229527 : List Nat := [1, 1, 3, 2, 1, 6, 2, 2, 4]
def baseStart_1229527 : Nat := 118140960795 + 1229527 * 2 ^ 59
def prefixEnd_1229527 : Nat := 4983230072969 + 3 ^ 40 * 1229527 * 2
def baseEnd_1229527 : Nat := 140297406373492489701781

theorem tailTrace_1229527 : CollatzResearch.WordTrace tailWord_1229527 prefixEnd_1229527 140297406373492489701781 := by
  unfold tailWord_1229527
  simp only [CollatzResearch.WordTrace]
  refine ⟨44844533816641140338830835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29896355877760760225887223 44844533816641140338830835)
  ·
    refine ⟨67266800724961710508246253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44844533816641140338830835 67266800724961710508246253)
    ·
      refine ⟨25225050271860641440592345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67266800724961710508246253 25225050271860641440592345)
      ·
        refine ⟨18918787703895481080444259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25225050271860641440592345 18918787703895481080444259)
        ·
          refine ⟨28378181555843221620666389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18918787703895481080444259 28378181555843221620666389)
          ·
            refine ⟨1330227260430151013468737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28378181555843221620666389 1330227260430151013468737)
            ·
              refine ⟨997670445322613260101553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330227260430151013468737 997670445322613260101553)
              ·
                refine ⟨748252833991959945076165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997670445322613260101553 748252833991959945076165)
                ·
                  refine ⟨140297406373492489701781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748252833991959945076165 140297406373492489701781)
                  ·
                    rfl

theorem cell22_1229527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 4].length) (baseStart_1229527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229527 prefixEnd_1229527 := by exact prefixLift 1229527
  have htrace : WordTrace (prefixWord ++ tailWord_1229527) baseStart_1229527 baseEnd_1229527 := by
    simpa [prefixWord, tailWord_1229527, baseEnd_1229527] using wordTrace_append hprefix tailTrace_1229527
  have hstable : (prefixWord ++ tailWord_1229527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229527).length < 2 ^ (prefixWord ++ tailWord_1229527).sum := by decide
  have hdescent : baseEnd_1229527 < baseStart_1229527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229536 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_1229536 : Nat := 118140960795 + 1229536 * 2 ^ 59
def prefixEnd_1229536 : Nat := 4983230072969 + 3 ^ 40 * 1229536 * 2
def baseEnd_1229536 : Nat := 420895300004404445630315

theorem tailTrace_1229536 : CollatzResearch.WordTrace tailWord_1229536 prefixEnd_1229536 420895300004404445630315 := by
  unfold tailWord_1229536
  simp only [CollatzResearch.WordTrace]
  refine ⟨22422431036804267437954231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29896574715739023250605641 22422431036804267437954231)
  ·
    refine ⟨33633646555206401156931347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22422431036804267437954231 33633646555206401156931347)
    ·
      refine ⟨50450469832809601735397021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33633646555206401156931347 50450469832809601735397021)
      ·
        refine ⟨18918926187303600650773883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50450469832809601735397021 18918926187303600650773883)
        ·
          refine ⟨28378389280955400976160825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18918926187303600650773883 28378389280955400976160825)
          ·
            refine ⟨21283791960716550732120619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28378389280955400976160825 21283791960716550732120619)
            ·
              refine ⟨31925687941074826098180929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21283791960716550732120619 31925687941074826098180929)
              ·
                refine ⟨23944265955806119573635697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31925687941074826098180929 23944265955806119573635697)
                ·
                  refine ⟨17958199466854589680226773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23944265955806119573635697 17958199466854589680226773)
                  ·
                    refine ⟨420895300004404445630315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17958199466854589680226773 420895300004404445630315)
                    ·
                      rfl

theorem cell22_1229536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_1229536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229536 prefixEnd_1229536 := by exact prefixLift 1229536
  have htrace : WordTrace (prefixWord ++ tailWord_1229536) baseStart_1229536 baseEnd_1229536 := by
    simpa [prefixWord, tailWord_1229536, baseEnd_1229536] using wordTrace_append hprefix tailTrace_1229536
  have hstable : (prefixWord ++ tailWord_1229536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229536).length < 2 ^ (prefixWord ++ tailWord_1229536).sum := by decide
  have hdescent : baseEnd_1229536 < baseStart_1229536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229638 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1229638 : Nat := 118140960795 + 1229638 * 2 ^ 59
def prefixEnd_1229638 : Nat := 4983230072969 + 3 ^ 40 * 1229638 * 2
def baseEnd_1229638 : Nat := 420930216688910179580003

theorem tailTrace_1229638 : CollatzResearch.WordTrace tailWord_1229638 prefixEnd_1229638 420930216688910179580003 := by
  unfold tailWord_1229638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401518197476218946753799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29899054879492670864081045 1401518197476218946753799)
  ·
    refine ⟨2102277296214328420130699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1401518197476218946753799 2102277296214328420130699)
    ·
      refine ⟨3153415944321492630196049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2102277296214328420130699 3153415944321492630196049)
      ·
        refine ⟨2365061958241119472647037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3153415944321492630196049 2365061958241119472647037)
        ·
          refine ⟨886898234340419802242639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2365061958241119472647037 886898234340419802242639)
          ·
            refine ⟨1330347351510629703363959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886898234340419802242639 1330347351510629703363959)
            ·
              refine ⟨1995521027265944555045939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330347351510629703363959 1995521027265944555045939)
              ·
                refine ⟨2993281540898916832568909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995521027265944555045939 2993281540898916832568909)
                ·
                  refine ⟨1122480577837093812213341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2993281540898916832568909 1122480577837093812213341)
                  ·
                    refine ⟨420930216688910179580003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1122480577837093812213341 420930216688910179580003)
                    ·
                      rfl

theorem cell22_1229638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1229638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229638 prefixEnd_1229638 := by exact prefixLift 1229638
  have htrace : WordTrace (prefixWord ++ tailWord_1229638) baseStart_1229638 baseEnd_1229638 := by
    simpa [prefixWord, tailWord_1229638, baseEnd_1229638] using wordTrace_append hprefix tailTrace_1229638
  have hstable : (prefixWord ++ tailWord_1229638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229638).length < 2 ^ (prefixWord ++ tailWord_1229638).sum := by decide
  have hdescent : baseEnd_1229638 < baseStart_1229638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229752 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 5]
def baseStart_1229752 : Nat := 118140960795 + 1229752 * 2 ^ 59
def prefixEnd_1229752 : Nat := 4983230072969 + 3 ^ 40 * 1229752 * 2
def baseEnd_1229752 : Nat := 140323080406217294076551

theorem tailTrace_1229752 : CollatzResearch.WordTrace tailWord_1229752 prefixEnd_1229752 140323080406217294076551 := by
  unfold tailWord_1229752
  simp only [CollatzResearch.WordTrace]
  refine ⟨22426370120413001882885755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29901826827217335843847673 22426370120413001882885755)
  ·
    refine ⟨33639555180619502824328633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22426370120413001882885755 33639555180619502824328633)
    ·
      refine ⟨25229666385464627118246475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33639555180619502824328633 25229666385464627118246475)
      ·
        refine ⟨37844499578196940677369713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25229666385464627118246475 37844499578196940677369713)
        ·
          refine ⟨28383374683647705508027285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37844499578196940677369713 28383374683647705508027285)
          ·
            refine ⟨1330470688295986195688779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28383374683647705508027285 1330470688295986195688779)
            ·
              refine ⟨1995706032443979293533169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330470688295986195688779 1995706032443979293533169)
              ·
                refine ⟨1496779524332984470149877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995706032443979293533169 1496779524332984470149877)
                ·
                  refine ⟨140323080406217294076551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1496779524332984470149877 140323080406217294076551)
                  ·
                    rfl

theorem cell22_1229752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_1229752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229752 prefixEnd_1229752 := by exact prefixLift 1229752
  have htrace : WordTrace (prefixWord ++ tailWord_1229752) baseStart_1229752 baseEnd_1229752 := by
    simpa [prefixWord, tailWord_1229752, baseEnd_1229752] using wordTrace_append hprefix tailTrace_1229752
  have hstable : (prefixWord ++ tailWord_1229752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229752).length < 2 ^ (prefixWord ++ tailWord_1229752).sum := by decide
  have hdescent : baseEnd_1229752 < baseStart_1229752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229763 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 10]
def baseStart_1229763 : Nat := 118140960795 + 1229763 * 2 ^ 59
def prefixEnd_1229763 : Nat := 4983230072969 + 3 ^ 40 * 1229763 * 2
def baseEnd_1229763 : Nat := 140324335581150506734873

theorem tailTrace_1229763 : CollatzResearch.WordTrace tailWord_1229763 prefixEnd_1229763 140324335581150506734873 := by
  unfold tailWord_1229763
  simp only [CollatzResearch.WordTrace]
  refine ⟨44853141443786152644421943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29902094295857435096281295 44853141443786152644421943)
  ·
    refine ⟨67279712165679228966632915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44853141443786152644421943 67279712165679228966632915)
    ·
      refine ⟨100919568248518843449949373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67279712165679228966632915 100919568248518843449949373)
      ·
        refine ⟨37844838093194566293731015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100919568248518843449949373 37844838093194566293731015)
        ·
          refine ⟨56767257139791849440596523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37844838093194566293731015 56767257139791849440596523)
          ·
            refine ⟨85150885709687774160894785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56767257139791849440596523 85150885709687774160894785)
            ·
              refine ⟨63863164282265830620671089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85150885709687774160894785 63863164282265830620671089)
              ·
                refine ⟨47897373211699372965503317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63863164282265830620671089 47897373211699372965503317)
                ·
                  refine ⟨140324335581150506734873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 47897373211699372965503317 140324335581150506734873)
                  ·
                    rfl

theorem cell22_1229763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 10].length) (baseStart_1229763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229763 prefixEnd_1229763 := by exact prefixLift 1229763
  have htrace : WordTrace (prefixWord ++ tailWord_1229763) baseStart_1229763 baseEnd_1229763 := by
    simpa [prefixWord, tailWord_1229763, baseEnd_1229763] using wordTrace_append hprefix tailTrace_1229763
  have hstable : (prefixWord ++ tailWord_1229763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229763).length < 2 ^ (prefixWord ++ tailWord_1229763).sum := by decide
  have hdescent : baseEnd_1229763 < baseStart_1229763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229795 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 3, 5]
def baseStart_1229795 : Nat := 118140960795 + 1229795 * 2 ^ 59
def prefixEnd_1229795 : Nat := 4983230072969 + 3 ^ 40 * 1229795 * 2
def baseEnd_1229795 : Nat := 420983960997414103404521

theorem tailTrace_1229795 : CollatzResearch.WordTrace tailWord_1229795 prefixEnd_1229795 420983960997414103404521 := by
  unfold tailWord_1229795
  simp only [CollatzResearch.WordTrace]
  refine ⟨44854308579670222109586839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29902872386446814739724559 44854308579670222109586839)
  ·
    refine ⟨67281462869505333164380259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44854308579670222109586839 67281462869505333164380259)
    ·
      refine ⟨100922194304257999746570389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67281462869505333164380259 100922194304257999746570389)
      ·
        refine ⟨4730727858012093738120487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100922194304257999746570389 4730727858012093738120487)
        ·
          refine ⟨7096091787018140607180731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4730727858012093738120487 7096091787018140607180731)
          ·
            refine ⟨10644137680527210910771097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096091787018140607180731 10644137680527210910771097)
            ·
              refine ⟨7983103260395408183078323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10644137680527210910771097 7983103260395408183078323)
              ·
                refine ⟨11974654890593112274617485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7983103260395408183078323 11974654890593112274617485)
                ·
                  refine ⟨4490495583972417102981557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11974654890593112274617485 4490495583972417102981557)
                  ·
                    refine ⟨420983960997414103404521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4490495583972417102981557 420983960997414103404521)
                    ·
                      rfl

theorem cell22_1229795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_1229795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229795 prefixEnd_1229795 := by exact prefixLift 1229795
  have htrace : WordTrace (prefixWord ++ tailWord_1229795) baseStart_1229795 baseEnd_1229795 := by
    simpa [prefixWord, tailWord_1229795, baseEnd_1229795] using wordTrace_append hprefix tailTrace_1229795
  have hstable : (prefixWord ++ tailWord_1229795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229795).length < 2 ^ (prefixWord ++ tailWord_1229795).sum := by decide
  have hdescent : baseEnd_1229795 < baseStart_1229795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229814 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_1229814 : Nat := 118140960795 + 1229814 * 2 ^ 59
def prefixEnd_1229814 : Nat := 4983230072969 + 3 ^ 40 * 1229814 * 2
def baseEnd_1229814 : Nat := 140330155028568129059821

theorem tailTrace_1229814 : CollatzResearch.WordTrace tailWord_1229814 prefixEnd_1229814 140330155028568129059821 := by
  unfold tailWord_1229814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2803437597912586772158031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29903334377734258903018997 2803437597912586772158031)
  ·
    refine ⟨4205156396868880158237047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2803437597912586772158031 4205156396868880158237047)
    ·
      refine ⟨6307734595303320237355571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4205156396868880158237047 6307734595303320237355571)
      ·
        refine ⟨9461601892954980356033357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6307734595303320237355571 9461601892954980356033357)
        ·
          refine ⟨3548100709858117633512509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9461601892954980356033357 3548100709858117633512509)
          ·
            refine ⟨1330537766196794112567191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3548100709858117633512509 1330537766196794112567191)
            ·
              refine ⟨1995806649295191168850787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330537766196794112567191 1995806649295191168850787)
              ·
                refine ⟨2993709973942786753276181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995806649295191168850787 2993709973942786753276181)
                ·
                  refine ⟨140330155028568129059821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2993709973942786753276181 140330155028568129059821)
                  ·
                    rfl

theorem cell22_1229814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_1229814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229814 prefixEnd_1229814 := by exact prefixLift 1229814
  have htrace : WordTrace (prefixWord ++ tailWord_1229814) baseStart_1229814 baseEnd_1229814 := by
    simpa [prefixWord, tailWord_1229814, baseEnd_1229814] using wordTrace_append hprefix tailTrace_1229814
  have hstable : (prefixWord ++ tailWord_1229814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229814).length < 2 ^ (prefixWord ++ tailWord_1229814).sum := by decide
  have hdescent : baseEnd_1229814 < baseStart_1229814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229825 : List Nat := [1, 2, 4, 1, 2, 2, 1, 9]
def baseStart_1229825 : Nat := 118140960795 + 1229825 * 2 ^ 59
def prefixEnd_1229825 : Nat := 4983230072969 + 3 ^ 40 * 1229825 * 2
def baseEnd_1229825 : Nat := 46777136734500447239381

theorem tailTrace_1229825 : CollatzResearch.WordTrace tailWord_1229825 prefixEnd_1229825 46777136734500447239381 := by
  unfold tailWord_1229825
  simp only [CollatzResearch.WordTrace]
  refine ⟨44855402769561537233178929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29903601846374358155452619 44855402769561537233178929)
  ·
    refine ⟨33641552077171152924884197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44855402769561537233178929 33641552077171152924884197)
    ·
      refine ⟨6307791014469591173415787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33641552077171152924884197 6307791014469591173415787)
      ·
        refine ⟨9461686521704386760123681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6307791014469591173415787 9461686521704386760123681)
        ·
          refine ⟨7096264891278290070092761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9461686521704386760123681 7096264891278290070092761)
          ·
            refine ⟨5322198668458717552569571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7096264891278290070092761 5322198668458717552569571)
            ·
              refine ⟨7983298002688076328854357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322198668458717552569571 7983298002688076328854357)
              ·
                refine ⟨46777136734500447239381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7983298002688076328854357 46777136734500447239381)
                ·
                  rfl

theorem cell22_1229825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 9].length) (baseStart_1229825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229825 prefixEnd_1229825 := by exact prefixLift 1229825
  have htrace : WordTrace (prefixWord ++ tailWord_1229825) baseStart_1229825 baseEnd_1229825 := by
    simpa [prefixWord, tailWord_1229825, baseEnd_1229825] using wordTrace_append hprefix tailTrace_1229825
  have hstable : (prefixWord ++ tailWord_1229825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229825).length < 2 ^ (prefixWord ++ tailWord_1229825).sum := by decide
  have hdescent : baseEnd_1229825 < baseStart_1229825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229932 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 6]
def baseStart_1229932 : Nat := 118140960795 + 1229932 * 2 ^ 59
def prefixEnd_1229932 : Nat := 4983230072969 + 3 ^ 40 * 1229932 * 2
def baseEnd_1229932 : Nat := 140343619632397137576367

theorem tailTrace_1229932 : CollatzResearch.WordTrace tailWord_1229932 prefixEnd_1229932 140343619632397137576367 := by
  unfold tailWord_1229932
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429652690086947253662025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29906203586782596338216033 22429652690086947253662025)
  ·
    refine ⟨16822239517565210440246519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22429652690086947253662025 16822239517565210440246519)
    ·
      refine ⟨25233359276347815660369779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16822239517565210440246519 25233359276347815660369779)
      ·
        refine ⟨37850038914521723490554669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25233359276347815660369779 37850038914521723490554669)
        ·
          refine ⟨14193764592945646308958001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37850038914521723490554669 14193764592945646308958001)
          ·
            refine ⟨10645323444709234731718501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14193764592945646308958001 10645323444709234731718501)
            ·
              refine ⟨1995998145882981512197219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10645323444709234731718501 1995998145882981512197219)
              ·
                refine ⟨2993997218824472268295829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995998145882981512197219 2993997218824472268295829)
                ·
                  refine ⟨140343619632397137576367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2993997218824472268295829 140343619632397137576367)
                  ·
                    rfl

theorem cell22_1229932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_1229932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229932 prefixEnd_1229932 := by exact prefixLift 1229932
  have htrace : WordTrace (prefixWord ++ tailWord_1229932) baseStart_1229932 baseEnd_1229932 := by
    simpa [prefixWord, tailWord_1229932, baseEnd_1229932] using wordTrace_append hprefix tailTrace_1229932
  have hstable : (prefixWord ++ tailWord_1229932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229932).length < 2 ^ (prefixWord ++ tailWord_1229932).sum := by decide
  have hdescent : baseEnd_1229932 < baseStart_1229932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229962 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1229962 : Nat := 118140960795 + 1229962 * 2 ^ 59
def prefixEnd_1229962 : Nat := 4983230072969 + 3 ^ 40 * 1229962 * 2
def baseEnd_1229962 : Nat := 421041128510281334479009

theorem tailTrace_1229962 : CollatzResearch.WordTrace tailWord_1229962 prefixEnd_1229962 421041128510281334479009 := by
  unfold tailWord_1229962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11215099892516302407729035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29906933046710139753944093 11215099892516302407729035)
  ·
    refine ⟨16822649838774453611593553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11215099892516302407729035 16822649838774453611593553)
    ·
      refine ⟨12616987379080840208695165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16822649838774453611593553 12616987379080840208695165)
      ·
        refine ⟨4731370267155315078260687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12616987379080840208695165 4731370267155315078260687)
        ·
          refine ⟨7097055400732972617391031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4731370267155315078260687 7097055400732972617391031)
          ·
            refine ⟨10645583101099458926086547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7097055400732972617391031 10645583101099458926086547)
            ·
              refine ⟨15968374651649188389129821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10645583101099458926086547 15968374651649188389129821)
              ·
                refine ⟨5988140494368445645923683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15968374651649188389129821 5988140494368445645923683)
                ·
                  refine ⟨8982210741552668468885525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5988140494368445645923683 8982210741552668468885525)
                  ·
                    refine ⟨421041128510281334479009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8982210741552668468885525 421041128510281334479009)
                    ·
                      rfl

theorem cell22_1229962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1229962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229962 prefixEnd_1229962 := by exact prefixLift 1229962
  have htrace : WordTrace (prefixWord ++ tailWord_1229962) baseStart_1229962 baseEnd_1229962 := by
    simpa [prefixWord, tailWord_1229962, baseEnd_1229962] using wordTrace_append hprefix tailTrace_1229962
  have hstable : (prefixWord ++ tailWord_1229962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229962).length < 2 ^ (prefixWord ++ tailWord_1229962).sum := by decide
  have hdescent : baseEnd_1229962 < baseStart_1229962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229966 : List Nat := [4, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_1229966 : Nat := 118140960795 + 1229966 * 2 ^ 59
def prefixEnd_1229966 : Nat := 4983230072969 + 3 ^ 40 * 1229966 * 2
def baseEnd_1229966 : Nat := 140347499264008885792999

theorem tailTrace_1229966 : CollatzResearch.WordTrace tailWord_1229966 prefixEnd_1229966 140347499264008885792999 := by
  unfold tailWord_1229966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5607568182756339789257719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29907030308033812209374501 5607568182756339789257719)
  ·
    refine ⟨8411352274134509683886579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5607568182756339789257719 8411352274134509683886579)
    ·
      refine ⟨12617028411201764525829869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8411352274134509683886579 12617028411201764525829869)
      ·
        refine ⟨4731385654200661697186201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12617028411201764525829869 4731385654200661697186201)
        ·
          refine ⟨3548539240650496272889651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4731385654200661697186201 3548539240650496272889651)
          ·
            refine ⟨5322808860975744409334477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548539240650496272889651 5322808860975744409334477)
            ·
              refine ⟨1996053322865904153500429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5322808860975744409334477 1996053322865904153500429)
              ·
                refine ⟨748519996074714057562661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1996053322865904153500429 748519996074714057562661)
                ·
                  refine ⟨140347499264008885792999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748519996074714057562661 140347499264008885792999)
                  ·
                    rfl

theorem cell22_1229966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_1229966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229966 prefixEnd_1229966 := by exact prefixLift 1229966
  have htrace : WordTrace (prefixWord ++ tailWord_1229966) baseStart_1229966 baseEnd_1229966 := by
    simpa [prefixWord, tailWord_1229966, baseEnd_1229966] using wordTrace_append hprefix tailTrace_1229966
  have hstable : (prefixWord ++ tailWord_1229966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229966).length < 2 ^ (prefixWord ++ tailWord_1229966).sum := by decide
  have hdescent : baseEnd_1229966 < baseStart_1229966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229983 : List Nat := [1, 1, 2, 6, 2, 1, 3, 2, 4]
def baseStart_1229983 : Nat := 118140960795 + 1229983 * 2 ^ 59
def prefixEnd_1229983 : Nat := 4983230072969 + 3 ^ 40 * 1229983 * 2
def baseEnd_1229983 : Nat := 140349439079814759901315

theorem tailTrace_1229983 : CollatzResearch.WordTrace tailWord_1229983 prefixEnd_1229983 140349439079814759901315 := by
  unfold tailWord_1229983
  simp only [CollatzResearch.WordTrace]
  refine ⟨44861165502989130217430603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29907443668659420144953735 44861165502989130217430603)
  ·
    refine ⟨67291748254483695326145905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44861165502989130217430603 67291748254483695326145905)
    ·
      refine ⟨50468811190862771494609429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67291748254483695326145905 50468811190862771494609429)
      ·
        refine ⟨2365725524571692413809817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50468811190862771494609429 2365725524571692413809817)
        ·
          refine ⟨1774294143428769310357363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2365725524571692413809817 1774294143428769310357363)
          ·
            refine ⟨2661441215143153965536045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774294143428769310357363 2661441215143153965536045)
            ·
              refine ⟨998040455678682737076017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2661441215143153965536045 998040455678682737076017)
              ·
                refine ⟨748530341759012052807013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998040455678682737076017 748530341759012052807013)
                ·
                  refine ⟨140349439079814759901315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748530341759012052807013 140349439079814759901315)
                  ·
                    rfl

theorem cell22_1229983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 4].length) (baseStart_1229983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229983 prefixEnd_1229983 := by exact prefixLift 1229983
  have htrace : WordTrace (prefixWord ++ tailWord_1229983) baseStart_1229983 baseEnd_1229983 := by
    simpa [prefixWord, tailWord_1229983, baseEnd_1229983] using wordTrace_append hprefix tailTrace_1229983
  have hstable : (prefixWord ++ tailWord_1229983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229983).length < 2 ^ (prefixWord ++ tailWord_1229983).sum := by decide
  have hdescent : baseEnd_1229983 < baseStart_1229983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1229994 : List Nat := [3, 1, 5, 1, 1, 1, 1, 9]
def baseStart_1229994 : Nat := 118140960795 + 1229994 * 2 ^ 59
def prefixEnd_1229994 : Nat := 4983230072969 + 3 ^ 40 * 1229994 * 2
def baseEnd_1229994 : Nat := 46783564751582657519879

theorem tailTrace_1229994 : CollatzResearch.WordTrace tailWord_1229994 prefixEnd_1229994 46783564751582657519879 := by
  unfold tailWord_1229994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11215391676487319774020259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29907711137299519397387357 11215391676487319774020259)
  ·
    refine ⟨16823087514730979661030389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11215391676487319774020259 16823087514730979661030389)
    ·
      refine ⟨1577164454506029343221599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16823087514730979661030389 1577164454506029343221599)
      ·
        refine ⟨2365746681759044014832399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577164454506029343221599 2365746681759044014832399)
        ·
          refine ⟨3548620022638566022248599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365746681759044014832399 3548620022638566022248599)
          ·
            refine ⟨5322930033957849033372899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3548620022638566022248599 5322930033957849033372899)
            ·
              refine ⟨7984395050936773550059349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322930033957849033372899 7984395050936773550059349)
              ·
                refine ⟨46783564751582657519879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7984395050936773550059349 46783564751582657519879)
                ·
                  rfl

theorem cell22_1229994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_1229994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1229994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1229994 prefixEnd_1229994 := by exact prefixLift 1229994
  have htrace : WordTrace (prefixWord ++ tailWord_1229994) baseStart_1229994 baseEnd_1229994 := by
    simpa [prefixWord, tailWord_1229994, baseEnd_1229994] using wordTrace_append hprefix tailTrace_1229994
  have hstable : (prefixWord ++ tailWord_1229994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1229994).length < 2 ^ (prefixWord ++ tailWord_1229994).sum := by decide
  have hdescent : baseEnd_1229994 < baseStart_1229994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1229994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230067 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 8]
def baseStart_1230067 : Nat := 118140960795 + 1230067 * 2 ^ 59
def prefixEnd_1230067 : Nat := 4983230072969 + 3 ^ 40 * 1230067 * 2
def baseEnd_1230067 : Nat := 140359024052032020201229

theorem tailTrace_1230067 : CollatzResearch.WordTrace tailWord_1230067 prefixEnd_1230067 140359024052032020201229 := by
  unfold tailWord_1230067
  simp only [CollatzResearch.WordTrace]
  refine ⟨44864229234684812563488455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29909486156456541708992303 44864229234684812563488455)
  ·
    refine ⟨67296343852027218845232683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44864229234684812563488455 67296343852027218845232683)
    ·
      refine ⟨100944515778040828267849025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67296343852027218845232683 100944515778040828267849025)
      ·
        refine ⟨75708386833530621200886769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100944515778040828267849025 75708386833530621200886769)
        ·
          refine ⟨56781290125147965900665077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75708386833530621200886769 56781290125147965900665077)
          ·
            refine ⟨5323245949232621803187351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56781290125147965900665077 5323245949232621803187351)
            ·
              refine ⟨7984868923848932704781027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5323245949232621803187351 7984868923848932704781027)
              ·
                refine ⟨11977303385773399057171541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7984868923848932704781027 11977303385773399057171541)
                ·
                  refine ⟨140359024052032020201229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11977303385773399057171541 140359024052032020201229)
                  ·
                    rfl

theorem cell22_1230067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 8].length) (baseStart_1230067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230067 prefixEnd_1230067 := by exact prefixLift 1230067
  have htrace : WordTrace (prefixWord ++ tailWord_1230067) baseStart_1230067 baseEnd_1230067 := by
    simpa [prefixWord, tailWord_1230067, baseEnd_1230067] using wordTrace_append hprefix tailTrace_1230067
  have hstable : (prefixWord ++ tailWord_1230067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230067).length < 2 ^ (prefixWord ++ tailWord_1230067).sum := by decide
  have hdescent : baseEnd_1230067 < baseStart_1230067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230127 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 1, 9]
def baseStart_1230127 : Nat := 118140960795 + 1230127 * 2 ^ 59
def prefixEnd_1230127 : Nat := 4983230072969 + 3 ^ 40 * 1230127 * 2
def baseEnd_1230127 : Nat := 421097611382275904103503

theorem tailTrace_1230127 : CollatzResearch.WordTrace tailWord_1230127 prefixEnd_1230127 421097611382275904103503 := by
  unfold tailWord_1230127
  simp only [CollatzResearch.WordTrace]
  refine ⟨44866417614467442810672635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29910945076311628540448423 44866417614467442810672635)
  ·
    refine ⟨67299626421701164216008953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44866417614467442810672635 67299626421701164216008953)
    ·
      refine ⟨50474719816275873162006715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67299626421701164216008953 50474719816275873162006715)
      ·
        refine ⟨75712079724413809743010073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50474719816275873162006715 75712079724413809743010073)
        ·
          refine ⟨56784059793310357307257555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75712079724413809743010073 56784059793310357307257555)
          ·
            refine ⟨85176089689965535960886333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56784059793310357307257555 85176089689965535960886333)
            ·
              refine ⟨31941033633737075985332375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85176089689965535960886333 31941033633737075985332375)
              ·
                refine ⟨47911550450605613977998563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31941033633737075985332375 47911550450605613977998563)
                ·
                  refine ⟨71867325675908420966997845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47911550450605613977998563 71867325675908420966997845)
                  ·
                    refine ⟨421097611382275904103503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 71867325675908420966997845 421097611382275904103503)
                    ·
                      rfl

theorem cell22_1230127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_1230127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230127 prefixEnd_1230127 := by exact prefixLift 1230127
  have htrace : WordTrace (prefixWord ++ tailWord_1230127) baseStart_1230127 baseEnd_1230127 := by
    simpa [prefixWord, tailWord_1230127, baseEnd_1230127] using wordTrace_append hprefix tailTrace_1230127
  have hstable : (prefixWord ++ tailWord_1230127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230127).length < 2 ^ (prefixWord ++ tailWord_1230127).sum := by decide
  have hdescent : baseEnd_1230127 < baseStart_1230127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230129 : List Nat := [1, 2, 2, 3, 3, 2, 1, 8]
def baseStart_1230129 : Nat := 118140960795 + 1230129 * 2 ^ 59
def prefixEnd_1230129 : Nat := 4983230072969 + 3 ^ 40 * 1230129 * 2
def baseEnd_1230129 : Nat := 46788699558127618394833

theorem tailTrace_1230129 : CollatzResearch.WordTrace tailWord_1230129 prefixEnd_1230129 46788699558127618394833 := by
  unfold tailWord_1230129
  simp only [CollatzResearch.WordTrace]
  refine ⟨44866490560460197152245441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29910993706973464768163627 44866490560460197152245441)
  ·
    refine ⟨33649867920345147864184081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44866490560460197152245441 33649867920345147864184081)
    ·
      refine ⟨25237400940258860898138061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33649867920345147864184081 25237400940258860898138061)
      ·
        refine ⟨9464025352597072836801773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25237400940258860898138061 9464025352597072836801773)
        ·
          refine ⟨3549009507223902313800665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9464025352597072836801773 3549009507223902313800665)
          ·
            refine ⟨2661757130417926735350499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3549009507223902313800665 2661757130417926735350499)
            ·
              refine ⟨3992635695626890103025749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661757130417926735350499 3992635695626890103025749)
              ·
                refine ⟨46788699558127618394833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3992635695626890103025749 46788699558127618394833)
                ·
                  rfl

theorem cell22_1230129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 8].length) (baseStart_1230129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230129 prefixEnd_1230129 := by exact prefixLift 1230129
  have htrace : WordTrace (prefixWord ++ tailWord_1230129) baseStart_1230129 baseEnd_1230129 := by
    simpa [prefixWord, tailWord_1230129, baseEnd_1230129] using wordTrace_append hprefix tailTrace_1230129
  have hstable : (prefixWord ++ tailWord_1230129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230129).length < 2 ^ (prefixWord ++ tailWord_1230129).sum := by decide
  have hdescent : baseEnd_1230129 < baseStart_1230129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230148 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1230148 : Nat := 118140960795 + 1230148 * 2 ^ 59
def prefixEnd_1230148 : Nat := 4983230072969 + 3 ^ 40 * 1230148 * 2
def baseEnd_1230148 : Nat := 421104800111438849328439

theorem tailTrace_1230148 : CollatzResearch.WordTrace tailWord_1230148 prefixEnd_1230148 421104800111438849328439 := by
  unfold tailWord_1230148
  simp only [CollatzResearch.WordTrace]
  refine ⟨22433591773695681698593549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29911455698260908931458065 22433591773695681698593549)
  ·
    refine ⟨8412596915135880636972581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22433591773695681698593549 8412596915135880636972581)
    ·
      refine ⟨1577361921587977619432359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8412596915135880636972581 1577361921587977619432359)
      ·
        refine ⟨2366042882381966429148539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577361921587977619432359 2366042882381966429148539)
        ·
          refine ⟨3549064323572949643722809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2366042882381966429148539 3549064323572949643722809)
          ·
            refine ⟨2661798242679712232792107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3549064323572949643722809 2661798242679712232792107)
            ·
              refine ⟨3992697364019568349188161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2661798242679712232792107 3992697364019568349188161)
              ·
                refine ⟨2994523023014676261891121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3992697364019568349188161 2994523023014676261891121)
                ·
                  refine ⟨2245892267261007196418341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2994523023014676261891121 2245892267261007196418341)
                  ·
                    refine ⟨421104800111438849328439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2245892267261007196418341 421104800111438849328439)
                    ·
                      rfl

theorem cell22_1230148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1230148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230148 prefixEnd_1230148 := by exact prefixLift 1230148
  have htrace : WordTrace (prefixWord ++ tailWord_1230148) baseStart_1230148 baseEnd_1230148 := by
    simpa [prefixWord, tailWord_1230148, baseEnd_1230148] using wordTrace_append hprefix tailTrace_1230148
  have hstable : (prefixWord ++ tailWord_1230148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230148).length < 2 ^ (prefixWord ++ tailWord_1230148).sum := by decide
  have hdescent : baseEnd_1230148 < baseStart_1230148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230212 : List Nat := [2, 3, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_1230212 : Nat := 118140960795 + 1230212 * 2 ^ 59
def prefixEnd_1230212 : Nat := 4983230072969 + 3 ^ 40 * 1230212 * 2
def baseEnd_1230212 : Nat := 421126708619364015728243

theorem tailTrace_1230212 : CollatzResearch.WordTrace tailWord_1230212 prefixEnd_1230212 421126708619364015728243 := by
  unfold tailWord_1230212
  simp only [CollatzResearch.WordTrace]
  refine ⟨22434758909579751163758445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29913011879439668218344593 22434758909579751163758445)
  ·
    refine ⟨8413034591092406686409417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22434758909579751163758445 8413034591092406686409417)
    ·
      refine ⟨6309775943319305014807063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8413034591092406686409417 6309775943319305014807063)
      ·
        refine ⟨9464663914978957522210595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6309775943319305014807063 9464663914978957522210595)
        ·
          refine ⟨14196995872468436283315893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9464663914978957522210595 14196995872468436283315893)
          ·
            refine ⟨1330968363043915901560865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14196995872468436283315893 1330968363043915901560865)
            ·
              refine ⟨998226272282936926170649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330968363043915901560865 998226272282936926170649)
              ·
                refine ⟨748669704212202694627987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998226272282936926170649 748669704212202694627987)
                ·
                  refine ⟨1123004556318304041941981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748669704212202694627987 1123004556318304041941981)
                  ·
                    refine ⟨421126708619364015728243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1123004556318304041941981 421126708619364015728243)
                    ·
                      rfl

theorem cell22_1230212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_1230212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230212 prefixEnd_1230212 := by exact prefixLift 1230212
  have htrace : WordTrace (prefixWord ++ tailWord_1230212) baseStart_1230212 baseEnd_1230212 := by
    simpa [prefixWord, tailWord_1230212, baseEnd_1230212] using wordTrace_append hprefix tailTrace_1230212
  have hstable : (prefixWord ++ tailWord_1230212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230212).length < 2 ^ (prefixWord ++ tailWord_1230212).sum := by decide
  have hdescent : baseEnd_1230212 < baseStart_1230212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230219 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 6]
def baseStart_1230219 : Nat := 118140960795 + 1230219 * 2 ^ 59
def prefixEnd_1230219 : Nat := 4983230072969 + 3 ^ 40 * 1230219 * 2
def baseEnd_1230219 : Nat := 140376368287472776934407

theorem tailTrace_1230219 : CollatzResearch.WordTrace tailWord_1230219 prefixEnd_1230219 140376368287472776934407 := by
  unfold tailWord_1230219
  simp only [CollatzResearch.WordTrace]
  refine ⟨44869773130134142523021711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29913182086756095015347807 44869773130134142523021711)
  ·
    refine ⟨67304659695201213784532567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44869773130134142523021711 67304659695201213784532567)
    ·
      refine ⟨100956989542801820676798851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67304659695201213784532567 100956989542801820676798851)
      ·
        refine ⟨151435484314202731015198277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100956989542801820676798851 151435484314202731015198277)
        ·
          refine ⟨28394153308913012065349677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151435484314202731015198277 28394153308913012065349677)
          ·
            refine ⟨10647807490842379524506129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28394153308913012065349677 10647807490842379524506129)
            ·
              refine ⟨7985855618131784643379597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10647807490842379524506129 7985855618131784643379597)
              ·
                refine ⟨2994695856799419241267349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7985855618131784643379597 2994695856799419241267349)
                ·
                  refine ⟨140376368287472776934407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2994695856799419241267349 140376368287472776934407)
                  ·
                    rfl

theorem cell22_1230219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 6].length) (baseStart_1230219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230219 prefixEnd_1230219 := by exact prefixLift 1230219
  have htrace : WordTrace (prefixWord ++ tailWord_1230219) baseStart_1230219 baseEnd_1230219 := by
    simpa [prefixWord, tailWord_1230219, baseEnd_1230219] using wordTrace_append hprefix tailTrace_1230219
  have hstable : (prefixWord ++ tailWord_1230219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230219).length < 2 ^ (prefixWord ++ tailWord_1230219).sum := by decide
  have hdescent : baseEnd_1230219 < baseStart_1230219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230298 : List Nat := [3, 1, 1, 2, 3, 4, 2, 6]
def baseStart_1230298 : Nat := 118140960795 + 1230298 * 2 ^ 59
def prefixEnd_1230298 : Nat := 4983230072969 + 3 ^ 40 * 1230298 * 2
def baseEnd_1230298 : Nat := 46795127575209828675331

theorem tailTrace_1230298 : CollatzResearch.WordTrace tailWord_1230298 prefixEnd_1230298 46795127575209828675331 := by
  unfold tailWord_1230298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218163624211984753786887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29915102997898626010098365 11218163624211984753786887)
  ·
    refine ⟨16827245436317977130680331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11218163624211984753786887 16827245436317977130680331)
    ·
      refine ⟨25240868154476965696020497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16827245436317977130680331 25240868154476965696020497)
      ·
        refine ⟨18930651115857724272015373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25240868154476965696020497 18930651115857724272015373)
        ·
          refine ⟨7098994168446646602005765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18930651115857724272015373 7098994168446646602005765)
          ·
            refine ⟨1331061406583746237876081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7098994168446646602005765 1331061406583746237876081)
            ·
              refine ⟨998296054937809678407061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1331061406583746237876081 998296054937809678407061)
              ·
                refine ⟨46795127575209828675331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 998296054937809678407061 46795127575209828675331)
                ·
                  rfl

theorem cell22_1230298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_1230298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230298 prefixEnd_1230298 := by exact prefixLift 1230298
  have htrace : WordTrace (prefixWord ++ tailWord_1230298) baseStart_1230298 baseEnd_1230298 := by
    simpa [prefixWord, tailWord_1230298, baseEnd_1230298] using wordTrace_append hprefix tailTrace_1230298
  have hstable : (prefixWord ++ tailWord_1230298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230298).length < 2 ^ (prefixWord ++ tailWord_1230298).sum := by decide
  have hdescent : baseEnd_1230298 < baseStart_1230298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230343 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 5]
def baseStart_1230343 : Nat := 118140960795 + 1230343 * 2 ^ 59
def prefixEnd_1230343 : Nat := 4983230072969 + 3 ^ 40 * 1230343 * 2
def baseEnd_1230343 : Nat := 140390517532174446900947

theorem tailTrace_1230343 : CollatzResearch.WordTrace tailWord_1230343 prefixEnd_1230343 140390517532174446900947 := by
  unfold tailWord_1230343
  simp only [CollatzResearch.WordTrace]
  refine ⟨44874295781684911700535683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29916197187789941133690455 44874295781684911700535683)
  ·
    refine ⟨67311443672527367550803525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44874295781684911700535683 67311443672527367550803525)
    ·
      refine ⟨12620895688598881415775661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67311443672527367550803525 12620895688598881415775661)
      ·
        refine ⟨4732835883224580530915873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12620895688598881415775661 4732835883224580530915873)
        ·
          refine ⟨3549626912418435398186905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4732835883224580530915873 3549626912418435398186905)
          ·
            refine ⟨2662220184313826548640179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3549626912418435398186905 2662220184313826548640179)
            ·
              refine ⟨3993330276470739822960269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662220184313826548640179 3993330276470739822960269)
              ·
                refine ⟨1497498853676527433610101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3993330276470739822960269 1497498853676527433610101)
                ·
                  refine ⟨140390517532174446900947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1497498853676527433610101 140390517532174446900947)
                  ·
                    rfl

theorem cell22_1230343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 5].length) (baseStart_1230343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230343 prefixEnd_1230343 := by exact prefixLift 1230343
  have htrace : WordTrace (prefixWord ++ tailWord_1230343) baseStart_1230343 baseEnd_1230343 := by
    simpa [prefixWord, tailWord_1230343, baseEnd_1230343] using wordTrace_append hprefix tailTrace_1230343
  have hstable : (prefixWord ++ tailWord_1230343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230343).length < 2 ^ (prefixWord ++ tailWord_1230343).sum := by decide
  have hdescent : baseEnd_1230343 < baseStart_1230343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230386 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1230386 : Nat := 118140960795 + 1230386 * 2 ^ 59
def prefixEnd_1230386 : Nat := 4983230072969 + 3 ^ 40 * 1230386 * 2
def baseEnd_1230386 : Nat := 421186272375285561877709

theorem tailTrace_1230386 : CollatzResearch.WordTrace tailWord_1230386 prefixEnd_1230386 421186272375285561877709 := by
  unfold tailWord_1230386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218966030132282511087753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29917242747019420029567341 11218966030132282511087753)
  ·
    refine ⟨8414224522599211883315815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11218966030132282511087753 8414224522599211883315815)
    ·
      refine ⟨12621336783898817824973723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8414224522599211883315815 12621336783898817824973723)
      ·
        refine ⟨18932005175848226737460585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12621336783898817824973723 18932005175848226737460585)
        ·
          refine ⟨14199003881886170053095439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18932005175848226737460585 14199003881886170053095439)
          ·
            refine ⟨21298505822829255079643159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14199003881886170053095439 21298505822829255079643159)
            ·
              refine ⟨31947758734243882619464739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21298505822829255079643159 31947758734243882619464739)
              ·
                refine ⟨47921638101365823929197109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31947758734243882619464739 47921638101365823929197109)
                ·
                  refine ⟨4492653572003045993362229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47921638101365823929197109 4492653572003045993362229)
                  ·
                    refine ⟨421186272375285561877709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4492653572003045993362229 421186272375285561877709)
                    ·
                      rfl

theorem cell22_1230386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1230386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230386 prefixEnd_1230386 := by exact prefixLift 1230386
  have htrace : WordTrace (prefixWord ++ tailWord_1230386) baseStart_1230386 baseEnd_1230386 := by
    simpa [prefixWord, tailWord_1230386, baseEnd_1230386] using wordTrace_append hprefix tailTrace_1230386
  have hstable : (prefixWord ++ tailWord_1230386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230386).length < 2 ^ (prefixWord ++ tailWord_1230386).sum := by decide
  have hdescent : baseEnd_1230386 < baseStart_1230386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230418 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1230418 : Nat := 118140960795 + 1230418 * 2 ^ 59
def prefixEnd_1230418 : Nat := 4983230072969 + 3 ^ 40 * 1230418 * 2
def baseEnd_1230418 : Nat := 421197226629248145077611

theorem tailTrace_1230418 : CollatzResearch.WordTrace tailWord_1230418 prefixEnd_1230418 421197226629248145077611 := by
  unfold tailWord_1230418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11219257814103299877378977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29918020837608799673010605 11219257814103299877378977)
  ·
    refine ⟨8414443360577474908034233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11219257814103299877378977 8414443360577474908034233)
    ·
      refine ⟨6310832520433106181025675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8414443360577474908034233 6310832520433106181025675)
      ·
        refine ⟨9466248780649659271538513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6310832520433106181025675 9466248780649659271538513)
        ·
          refine ⟨7099686585487244453653885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9466248780649659271538513 7099686585487244453653885)
          ·
            refine ⟨2662382469557716670120207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7099686585487244453653885 2662382469557716670120207)
            ·
              refine ⟨3993573704336575005180311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2662382469557716670120207 3993573704336575005180311)
              ·
                refine ⟨5990360556504862507770467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3993573704336575005180311 5990360556504862507770467)
                ·
                  refine ⟨8985540834757293761655701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5990360556504862507770467 8985540834757293761655701)
                  ·
                    refine ⟨421197226629248145077611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8985540834757293761655701 421197226629248145077611)
                    ·
                      rfl

theorem cell22_1230418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1230418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230418 prefixEnd_1230418 := by exact prefixLift 1230418
  have htrace : WordTrace (prefixWord ++ tailWord_1230418) baseStart_1230418 baseEnd_1230418 := by
    simpa [prefixWord, tailWord_1230418, baseEnd_1230418] using wordTrace_append hprefix tailTrace_1230418
  have hstable : (prefixWord ++ tailWord_1230418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230418).length < 2 ^ (prefixWord ++ tailWord_1230418).sum := by decide
  have hdescent : baseEnd_1230418 < baseStart_1230418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230437 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_1230437 : Nat := 118140960795 + 1230437 * 2 ^ 59
def prefixEnd_1230437 : Nat := 4983230072969 + 3 ^ 40 * 1230437 * 2
def baseEnd_1230437 : Nat := 421203730717538428852553

theorem tailTrace_1230437 : CollatzResearch.WordTrace tailWord_1230437 prefixEnd_1230437 421203730717538428852553 := by
  unfold tailWord_1230437
  simp only [CollatzResearch.WordTrace]
  refine ⟨44877724243344365754457565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29918482828896243836305043 44877724243344365754457565)
  ·
    refine ⟨16829146591254137157921587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44877724243344365754457565 16829146591254137157921587)
    ·
      refine ⟨25243719886881205736882381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16829146591254137157921587 25243719886881205736882381)
      ·
        refine ⟨9466394957580452151330893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25243719886881205736882381 9466394957580452151330893)
        ·
          refine ⟨3549898109092669556749085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9466394957580452151330893 3549898109092669556749085)
          ·
            refine ⟨1331211790909751083780907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3549898109092669556749085 1331211790909751083780907)
            ·
              refine ⟨1996817686364626625671361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331211790909751083780907 1996817686364626625671361)
              ·
                refine ⟨1497613264773469969253521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1996817686364626625671361 1497613264773469969253521)
                ·
                  refine ⟨1123209948580102476940141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1497613264773469969253521 1123209948580102476940141)
                  ·
                    refine ⟨421203730717538428852553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1123209948580102476940141 421203730717538428852553)
                    ·
                      rfl

theorem cell22_1230437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_1230437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230437 prefixEnd_1230437 := by exact prefixLift 1230437
  have htrace : WordTrace (prefixWord ++ tailWord_1230437) baseStart_1230437 baseEnd_1230437 := by
    simpa [prefixWord, tailWord_1230437, baseEnd_1230437] using wordTrace_append hprefix tailTrace_1230437
  have hstable : (prefixWord ++ tailWord_1230437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230437).length < 2 ^ (prefixWord ++ tailWord_1230437).sum := by decide
  have hdescent : baseEnd_1230437 < baseStart_1230437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230454 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_1230454 : Nat := 118140960795 + 1230454 * 2 ^ 59
def prefixEnd_1230454 : Nat := 4983230072969 + 3 ^ 40 * 1230454 * 2
def baseEnd_1230454 : Nat := 421209550164956051177501

theorem tailTrace_1230454 : CollatzResearch.WordTrace tailWord_1230454 prefixEnd_1230454 421209550164956051177501 := by
  unfold tailWord_1230454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804896517767673603614151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29918896189521851771884277 2804896517767673603614151)
  ·
    refine ⟨4207344776651510405421227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2804896517767673603614151 4207344776651510405421227)
    ·
      refine ⟨6311017164977265608131841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4207344776651510405421227 6311017164977265608131841)
      ·
        refine ⟨4733262873732949206098881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6311017164977265608131841 4733262873732949206098881)
        ·
          refine ⟨3549947155299711904574161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4733262873732949206098881 3549947155299711904574161)
          ·
            refine ⟨2662460366474783928430621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3549947155299711904574161 2662460366474783928430621)
            ·
              refine ⟨998422637428043973161483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662460366474783928430621 998422637428043973161483)
              ·
                refine ⟨1497633956142065959742225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998422637428043973161483 1497633956142065959742225)
                ·
                  refine ⟨1123225467106549469806669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1497633956142065959742225 1123225467106549469806669)
                  ·
                    refine ⟨421209550164956051177501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1123225467106549469806669 421209550164956051177501)
                    ·
                      rfl

theorem cell22_1230454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_1230454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230454 prefixEnd_1230454 := by exact prefixLift 1230454
  have htrace : WordTrace (prefixWord ++ tailWord_1230454) baseStart_1230454 baseEnd_1230454 := by
    simpa [prefixWord, tailWord_1230454, baseEnd_1230454] using wordTrace_append hprefix tailTrace_1230454
  have hstable : (prefixWord ++ tailWord_1230454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230454).length < 2 ^ (prefixWord ++ tailWord_1230454).sum := by decide
  have hdescent : baseEnd_1230454 < baseStart_1230454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230465 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1230465 : Nat := 118140960795 + 1230465 * 2 ^ 59
def prefixEnd_1230465 : Nat := 4983230072969 + 3 ^ 40 * 1230465 * 2
def baseEnd_1230465 : Nat := 421213315689755689152467

theorem tailTrace_1230465 : CollatzResearch.WordTrace tailWord_1230465 prefixEnd_1230465 421213315689755689152467 := by
  unfold tailWord_1230465
  simp only [CollatzResearch.WordTrace]
  refine ⟨44878745487242926536476849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29919163658161951024317899 44878745487242926536476849)
  ·
    refine ⟨33659059115432194902357637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44878745487242926536476849 33659059115432194902357637)
    ·
      refine ⟨6311073584143536544192057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33659059115432194902357637 6311073584143536544192057)
      ·
        refine ⟨4733305188107652408144043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6311073584143536544192057 4733305188107652408144043)
        ·
          refine ⟨7099957782161478612216065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4733305188107652408144043 7099957782161478612216065)
          ·
            refine ⟨5324968336621108959162049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7099957782161478612216065 5324968336621108959162049)
            ·
              refine ⟨3993726252465831719371537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5324968336621108959162049 3993726252465831719371537)
              ·
                refine ⟨2995294689349373789528653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3993726252465831719371537 2995294689349373789528653)
                ·
                  refine ⟨1123235508506015171073245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2995294689349373789528653 1123235508506015171073245)
                  ·
                    refine ⟨421213315689755689152467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1123235508506015171073245 421213315689755689152467)
                    ·
                      rfl

theorem cell22_1230465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1230465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230465 prefixEnd_1230465 := by exact prefixLift 1230465
  have htrace : WordTrace (prefixWord ++ tailWord_1230465) baseStart_1230465 baseEnd_1230465 := by
    simpa [prefixWord, tailWord_1230465, baseEnd_1230465] using wordTrace_append hprefix tailTrace_1230465
  have hstable : (prefixWord ++ tailWord_1230465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230465).length < 2 ^ (prefixWord ++ tailWord_1230465).sum := by decide
  have hdescent : baseEnd_1230465 < baseStart_1230465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230478 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_1230478 : Nat := 118140960795 + 1230478 * 2 ^ 59
def prefixEnd_1230478 : Nat := 4983230072969 + 3 ^ 40 * 1230478 * 2
def baseEnd_1230478 : Nat := 140405921951809329525809

theorem tailTrace_1230478 : CollatzResearch.WordTrace tailWord_1230478 prefixEnd_1230478 140405921951809329525809 := by
  unfold tailWord_1230478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5609902454524478719587511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29919479757463886504466725 5609902454524478719587511)
  ·
    refine ⟨8414853681786718079381267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5609902454524478719587511 8414853681786718079381267)
    ·
      refine ⟨12622280522680077119071901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8414853681786718079381267 12622280522680077119071901)
      ·
        refine ⟨4733355196005028919651963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12622280522680077119071901 4733355196005028919651963)
        ·
          refine ⟨7100032794007543379477945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4733355196005028919651963 7100032794007543379477945)
          ·
            refine ⟨5325024595505657534608459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7100032794007543379477945 5325024595505657534608459)
            ·
              refine ⟨7987536893258486301912689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5325024595505657534608459 7987536893258486301912689)
              ·
                refine ⟨5990652669943864726434517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7987536893258486301912689 5990652669943864726434517)
                ·
                  refine ⟨140405921951809329525809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5990652669943864726434517 140405921951809329525809)
                  ·
                    rfl

theorem cell22_1230478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_1230478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230478 prefixEnd_1230478 := by exact prefixLift 1230478
  have htrace : WordTrace (prefixWord ++ tailWord_1230478) baseStart_1230478 baseEnd_1230478 := by
    simpa [prefixWord, tailWord_1230478, baseEnd_1230478] using wordTrace_append hprefix tailTrace_1230478
  have hstable : (prefixWord ++ tailWord_1230478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230478).length < 2 ^ (prefixWord ++ tailWord_1230478).sum := by decide
  have hdescent : baseEnd_1230478 < baseStart_1230478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230542 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_1230542 : Nat := 118140960795 + 1230542 * 2 ^ 59
def prefixEnd_1230542 : Nat := 4983230072969 + 3 ^ 40 * 1230542 * 2
def baseEnd_1230542 : Nat := 421239674363353154977231

theorem tailTrace_1230542 : CollatzResearch.WordTrace tailWord_1230542 prefixEnd_1230542 421239674363353154977231 := by
  unfold tailWord_1230542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610194238495496085878735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29921035938642645791353253 5610194238495496085878735)
  ·
    refine ⟨8415291357743244128818103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5610194238495496085878735 8415291357743244128818103)
    ·
      refine ⟨12622937036614866193227155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8415291357743244128818103 12622937036614866193227155)
      ·
        refine ⟨18934405554922299289840733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12622937036614866193227155 18934405554922299289840733)
        ·
          refine ⟨7100402083095862233690275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18934405554922299289840733 7100402083095862233690275)
          ·
            refine ⟨10650603124643793350535413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7100402083095862233690275 10650603124643793350535413)
            ·
              refine ⟨998494042935355626612695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10650603124643793350535413 998494042935355626612695)
              ·
                refine ⟨1497741064403033439919043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998494042935355626612695 1497741064403033439919043)
                ·
                  refine ⟨2246611596604550159878565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497741064403033439919043 2246611596604550159878565)
                  ·
                    refine ⟨421239674363353154977231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2246611596604550159878565 421239674363353154977231)
                    ·
                      rfl

theorem cell22_1230542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_1230542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230542 prefixEnd_1230542 := by exact prefixLift 1230542
  have htrace : WordTrace (prefixWord ++ tailWord_1230542) baseStart_1230542 baseEnd_1230542 := by
    simpa [prefixWord, tailWord_1230542, baseEnd_1230542] using wordTrace_append hprefix tailTrace_1230542
  have hstable : (prefixWord ++ tailWord_1230542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230542).length < 2 ^ (prefixWord ++ tailWord_1230542).sum := by decide
  have hdescent : baseEnd_1230542 < baseStart_1230542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230550 : List Nat := [5, 2, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1230550 : Nat := 118140960795 + 1230550 * 2 ^ 59
def prefixEnd_1230550 : Nat := 4983230072969 + 3 ^ 40 * 1230550 * 2
def baseEnd_1230550 : Nat := 421242412926843800777207

theorem tailTrace_1230550 : CollatzResearch.WordTrace tailWord_1230550 prefixEnd_1230550 421242412926843800777207 := by
  unfold tailWord_1230550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2805115355745936628332569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29921230461289990702214069 2805115355745936628332569)
  ·
    refine ⟨2103836516809452471249427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2805115355745936628332569 2103836516809452471249427)
    ·
      refine ⟨3155754775214178706874141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2103836516809452471249427 3155754775214178706874141)
      ·
        refine ⟨1183408040705317015077803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3155754775214178706874141 1183408040705317015077803)
        ·
          refine ⟨1775112061057975522616705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183408040705317015077803 1775112061057975522616705)
          ·
            refine ⟨1331334045793481641962529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775112061057975522616705 1331334045793481641962529)
            ·
              refine ⟨998500534345111231471897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1331334045793481641962529 998500534345111231471897)
              ·
                refine ⟨748875400758833423603923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998500534345111231471897 748875400758833423603923)
                ·
                  refine ⟨1123313101138250135405885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748875400758833423603923 1123313101138250135405885)
                  ·
                    refine ⟨421242412926843800777207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1123313101138250135405885 421242412926843800777207)
                    ·
                      rfl

theorem cell22_1230550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1230550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230550 prefixEnd_1230550 := by exact prefixLift 1230550
  have htrace : WordTrace (prefixWord ++ tailWord_1230550) baseStart_1230550 baseEnd_1230550 := by
    simpa [prefixWord, tailWord_1230550, baseEnd_1230550] using wordTrace_append hprefix tailTrace_1230550
  have hstable : (prefixWord ++ tailWord_1230550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230550).length < 2 ^ (prefixWord ++ tailWord_1230550).sum := by decide
  have hdescent : baseEnd_1230550 < baseStart_1230550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230600 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 5, 3]
def baseStart_1230600 : Nat := 118140960795 + 1230600 * 2 ^ 59
def prefixEnd_1230600 : Nat := 4983230072969 + 3 ^ 40 * 1230600 * 2
def baseEnd_1230600 : Nat := 421259528948660337027053

theorem tailTrace_1230600 : CollatzResearch.WordTrace tailWord_1230600 prefixEnd_1230600 421259528948660337027053 := by
  unfold tailWord_1230600
  simp only [CollatzResearch.WordTrace]
  refine ⟨22441834670876922296320627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29922446227835896395094169 22441834670876922296320627)
  ·
    refine ⟨33662752006315383444480941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22441834670876922296320627 33662752006315383444480941)
    ·
      refine ⟨12623532002368268791680353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33662752006315383444480941 12623532002368268791680353)
      ·
        refine ⟨9467649001776201593760265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12623532002368268791680353 9467649001776201593760265)
        ·
          refine ⟨7100736751332151195320199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9467649001776201593760265 7100736751332151195320199)
          ·
            refine ⟨10651105126998226792980299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7100736751332151195320199 10651105126998226792980299)
            ·
              refine ⟨15976657690497340189470449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10651105126998226792980299 15976657690497340189470449)
              ·
                refine ⟨11982493267873005142102837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15976657690497340189470449 11982493267873005142102837)
                ·
                  refine ⟨1123358743863094232072141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11982493267873005142102837 1123358743863094232072141)
                  ·
                    refine ⟨421259528948660337027053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1123358743863094232072141 421259528948660337027053)
                    ·
                      rfl

theorem cell22_1230600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_1230600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230600 prefixEnd_1230600 := by exact prefixLift 1230600
  have htrace : WordTrace (prefixWord ++ tailWord_1230600) baseStart_1230600 baseEnd_1230600 := by
    simpa [prefixWord, tailWord_1230600, baseEnd_1230600] using wordTrace_append hprefix tailTrace_1230600
  have hstable : (prefixWord ++ tailWord_1230600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230600).length < 2 ^ (prefixWord ++ tailWord_1230600).sum := by decide
  have hdescent : baseEnd_1230600 < baseStart_1230600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230754 : List Nat := [3, 3, 1, 2, 3, 1, 3, 6]
def baseStart_1230754 : Nat := 118140960795 + 1230754 * 2 ^ 59
def prefixEnd_1230754 : Nat := 4983230072969 + 3 ^ 40 * 1230754 * 2
def baseEnd_1230754 : Nat := 46812471810650585408509

theorem tailTrace_1230754 : CollatzResearch.WordTrace tailWord_1230754 prefixEnd_1230754 46812471810650585408509 := by
  unfold tailWord_1230754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11222321545798982223436829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29926190788797285929164877 11222321545798982223436829)
  ·
    refine ⟨4208370579674618333788811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11222321545798982223436829 4208370579674618333788811)
    ·
      refine ⟨6312555869511927500683217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208370579674618333788811 6312555869511927500683217)
      ·
        refine ⟨4734416902133945625512413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6312555869511927500683217 4734416902133945625512413)
        ·
          refine ⟨1775406338300229609567155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4734416902133945625512413 1775406338300229609567155)
          ·
            refine ⟨2663109507450344414350733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775406338300229609567155 2663109507450344414350733)
            ·
              refine ⟨998666065293879155381525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2663109507450344414350733 998666065293879155381525)
              ·
                refine ⟨46812471810650585408509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 998666065293879155381525 46812471810650585408509)
                ·
                  rfl

theorem cell22_1230754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_1230754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230754 prefixEnd_1230754 := by exact prefixLift 1230754
  have htrace : WordTrace (prefixWord ++ tailWord_1230754) baseStart_1230754 baseEnd_1230754 := by
    simpa [prefixWord, tailWord_1230754, baseEnd_1230754] using wordTrace_append hprefix tailTrace_1230754
  have hstable : (prefixWord ++ tailWord_1230754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230754).length < 2 ^ (prefixWord ++ tailWord_1230754).sum := by decide
  have hdescent : baseEnd_1230754 < baseStart_1230754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230782 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1230782 : Nat := 118140960795 + 1230782 * 2 ^ 59
def prefixEnd_1230782 : Nat := 4983230072969 + 3 ^ 40 * 1230782 * 2
def baseEnd_1230782 : Nat := 140440610422690842992165

theorem tailTrace_1230782 : CollatzResearch.WordTrace tailWord_1230782 prefixEnd_1230782 140440610422690842992165 := by
  unfold tailWord_1230782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611288428386811209470825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29926871618062993117177733 5611288428386811209470825)
  ·
    refine ⟨4208466321290108407103119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5611288428386811209470825 4208466321290108407103119)
    ·
      refine ⟨6312699481935162610654679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208466321290108407103119 6312699481935162610654679)
      ·
        refine ⟨9469049222902743915982019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6312699481935162610654679 9469049222902743915982019)
        ·
          refine ⟨14203573834354115873973029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9469049222902743915982019 14203573834354115873973029)
          ·
            refine ⟨2663170093941396726369943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14203573834354115873973029 2663170093941396726369943)
            ·
              refine ⟨3994755140912095089554915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663170093941396726369943 3994755140912095089554915)
              ·
                refine ⟨5992132711368142634332373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3994755140912095089554915 5992132711368142634332373)
                ·
                  refine ⟨140440610422690842992165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5992132711368142634332373 140440610422690842992165)
                  ·
                    rfl

theorem cell22_1230782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1230782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230782 prefixEnd_1230782 := by exact prefixLift 1230782
  have htrace : WordTrace (prefixWord ++ tailWord_1230782) baseStart_1230782 baseEnd_1230782 := by
    simpa [prefixWord, tailWord_1230782, baseEnd_1230782] using wordTrace_append hprefix tailTrace_1230782
  have hstable : (prefixWord ++ tailWord_1230782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230782).length < 2 ^ (prefixWord ++ tailWord_1230782).sum := by decide
  have hdescent : baseEnd_1230782 < baseStart_1230782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230859 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 2, 3]
def baseStart_1230859 : Nat := 118140960795 + 1230859 * 2 ^ 59
def prefixEnd_1230859 : Nat := 4983230072969 + 3 ^ 40 * 1230859 * 2
def baseEnd_1230859 : Nat := 421348189941669994801259

theorem tailTrace_1230859 : CollatzResearch.WordTrace tailWord_1230859 prefixEnd_1230859 421348189941669994801259 := by
  unfold tailWord_1230859
  simp only [CollatzResearch.WordTrace]
  refine ⟨44893115847815531826319631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29928743898543687884213087 44893115847815531826319631)
  ·
    refine ⟨67339673771723297739479447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44893115847815531826319631 67339673771723297739479447)
    ·
      refine ⟨101009510657584946609219171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67339673771723297739479447 101009510657584946609219171)
      ·
        refine ⟨151514265986377419913828757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101009510657584946609219171 151514265986377419913828757)
        ·
          refine ⟨7102231218111441558460723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 151514265986377419913828757 7102231218111441558460723)
          ·
            refine ⟨10653346827167162337691085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7102231218111441558460723 10653346827167162337691085)
            ·
              refine ⟨3995005060187685876634157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10653346827167162337691085 3995005060187685876634157)
              ·
                refine ⟨1498126897570382203737809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3995005060187685876634157 1498126897570382203737809)
                ·
                  refine ⟨1123595173177786652803357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1498126897570382203737809 1123595173177786652803357)
                  ·
                    refine ⟨421348189941669994801259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1123595173177786652803357 421348189941669994801259)
                    ·
                      rfl

theorem cell22_1230859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 3].length) (baseStart_1230859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230859 prefixEnd_1230859 := by exact prefixLift 1230859
  have htrace : WordTrace (prefixWord ++ tailWord_1230859) baseStart_1230859 baseEnd_1230859 := by
    simpa [prefixWord, tailWord_1230859, baseEnd_1230859] using wordTrace_append hprefix tailTrace_1230859
  have hstable : (prefixWord ++ tailWord_1230859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230859).length < 2 ^ (prefixWord ++ tailWord_1230859).sum := by decide
  have hdescent : baseEnd_1230859 < baseStart_1230859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230874 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_1230874 : Nat := 118140960795 + 1230874 * 2 ^ 59
def prefixEnd_1230874 : Nat := 4983230072969 + 3 ^ 40 * 1230874 * 2
def baseEnd_1230874 : Nat := 421353324748214955676213

theorem tailTrace_1230874 : CollatzResearch.WordTrace tailWord_1230874 prefixEnd_1230874 421353324748214955676213 := by
  unfold tailWord_1230874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11223415735690297347028919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29929108628507459592077117 11223415735690297347028919)
  ·
    refine ⟨16835123603535446020543379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11223415735690297347028919 16835123603535446020543379)
    ·
      refine ⟨25252685405303169030815069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16835123603535446020543379 25252685405303169030815069)
      ·
        refine ⟨9469757026988688386555651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25252685405303169030815069 9469757026988688386555651)
        ·
          refine ⟨14204635540483032579833477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9469757026988688386555651 14204635540483032579833477)
          ·
            refine ⟨2663369163840568608718777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14204635540483032579833477 2663369163840568608718777)
            ·
              refine ⟨1997526872880426456539083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663369163840568608718777 1997526872880426456539083)
              ·
                refine ⟨2996290309320639684808625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1997526872880426456539083 2996290309320639684808625)
                ·
                  refine ⟨2247217731990479763606469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996290309320639684808625 2247217731990479763606469)
                  ·
                    refine ⟨421353324748214955676213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247217731990479763606469 421353324748214955676213)
                    ·
                      rfl

theorem cell22_1230874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_1230874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230874 prefixEnd_1230874 := by exact prefixLift 1230874
  have htrace : WordTrace (prefixWord ++ tailWord_1230874) baseStart_1230874 baseEnd_1230874 := by
    simpa [prefixWord, tailWord_1230874, baseEnd_1230874] using wordTrace_append hprefix tailTrace_1230874
  have hstable : (prefixWord ++ tailWord_1230874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230874).length < 2 ^ (prefixWord ++ tailWord_1230874).sum := by decide
  have hdescent : baseEnd_1230874 < baseStart_1230874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230932 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1230932 : Nat := 118140960795 + 1230932 * 2 ^ 59
def prefixEnd_1230932 : Nat := 4983230072969 + 3 ^ 40 * 1230932 * 2
def baseEnd_1230932 : Nat := 421373179333522137726035

theorem tailTrace_1230932 : CollatzResearch.WordTrace tailWord_1230932 prefixEnd_1230932 421373179333522137726035 := by
  unfold tailWord_1230932
  simp only [CollatzResearch.WordTrace]
  refine ⟨22447889188275532646863525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29930518917700710195818033 22447889188275532646863525)
  ·
    refine ⟨4208979222801662371286911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22447889188275532646863525 4208979222801662371286911)
    ·
      refine ⟨6313468834202493556930367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208979222801662371286911 6313468834202493556930367)
      ·
        refine ⟨9470203251303740335395551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6313468834202493556930367 9470203251303740335395551)
        ·
          refine ⟨14205304876955610503093327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9470203251303740335395551 14205304876955610503093327)
          ·
            refine ⟨21307957315433415754639991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14205304876955610503093327 21307957315433415754639991)
            ·
              refine ⟨31961935973150123631959987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21307957315433415754639991 31961935973150123631959987)
              ·
                refine ⟨47942903959725185447939981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31961935973150123631959987 47942903959725185447939981)
                ·
                  refine ⟨17978588984896944542977493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47942903959725185447939981 17978588984896944542977493)
                  ·
                    refine ⟨421373179333522137726035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17978588984896944542977493 421373179333522137726035)
                    ·
                      rfl

theorem cell22_1230932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1230932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230932 prefixEnd_1230932 := by exact prefixLift 1230932
  have htrace : WordTrace (prefixWord ++ tailWord_1230932) baseStart_1230932 baseEnd_1230932 := by
    simpa [prefixWord, tailWord_1230932, baseEnd_1230932] using wordTrace_append hprefix tailTrace_1230932
  have hstable : (prefixWord ++ tailWord_1230932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230932).length < 2 ^ (prefixWord ++ tailWord_1230932).sum := by decide
  have hdescent : baseEnd_1230932 < baseStart_1230932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230981 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_1230981 : Nat := 118140960795 + 1230981 * 2 ^ 59
def prefixEnd_1230981 : Nat := 4983230072969 + 3 ^ 40 * 1230981 * 2
def baseEnd_1230981 : Nat := 421389953034902343250885

theorem tailTrace_1230981 : CollatzResearch.WordTrace tailWord_1230981 prefixEnd_1230981 421389953034902343250885 := by
  unfold tailWord_1230981
  simp only [CollatzResearch.WordTrace]
  refine ⟨44897565553373546662260797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29931710368915697774840531 44897565553373546662260797)
  ·
    refine ⟨16836587082515079998347799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44897565553373546662260797 16836587082515079998347799)
    ·
      refine ⟨25254880623772619997521699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16836587082515079998347799 25254880623772619997521699)
      ·
        refine ⟨37882320935658929996282549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25254880623772619997521699 37882320935658929996282549)
        ·
          refine ⟨3551467587718024687151489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37882320935658929996282549 3551467587718024687151489)
          ·
            refine ⟨2663600690788518515363617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3551467587718024687151489 2663600690788518515363617)
            ·
              refine ⟨1997700518091388886522713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663600690788518515363617 1997700518091388886522713)
              ·
                refine ⟨1498275388568541664892035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997700518091388886522713 1498275388568541664892035)
                ·
                  refine ⟨2247413082852812497338053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498275388568541664892035 2247413082852812497338053)
                  ·
                    refine ⟨421389953034902343250885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247413082852812497338053 421389953034902343250885)
                    ·
                      rfl

theorem cell22_1230981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_1230981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230981 prefixEnd_1230981 := by exact prefixLift 1230981
  have htrace : WordTrace (prefixWord ++ tailWord_1230981) baseStart_1230981 baseEnd_1230981 := by
    simpa [prefixWord, tailWord_1230981, baseEnd_1230981] using wordTrace_append hprefix tailTrace_1230981
  have hstable : (prefixWord ++ tailWord_1230981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230981).length < 2 ^ (prefixWord ++ tailWord_1230981).sum := by decide
  have hdescent : baseEnd_1230981 < baseStart_1230981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230992 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_1230992 : Nat := 118140960795 + 1230992 * 2 ^ 59
def prefixEnd_1230992 : Nat := 4983230072969 + 3 ^ 40 * 1230992 * 2
def baseEnd_1230992 : Nat := 421393718559701981225851

theorem tailTrace_1230992 : CollatzResearch.WordTrace tailWord_1230992 prefixEnd_1230992 421393718559701981225851 := by
  unfold tailWord_1230992
  simp only [CollatzResearch.WordTrace]
  refine ⟨22448983378166847770455615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29931977837555797027274153 22448983378166847770455615)
  ·
    refine ⟨33673475067250271655683423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22448983378166847770455615 33673475067250271655683423)
    ·
      refine ⟨50510212600875407483525135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33673475067250271655683423 50510212600875407483525135)
      ·
        refine ⟨75765318901313111225287703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50510212600875407483525135 75765318901313111225287703)
        ·
          refine ⟨113647978351969666837931555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75765318901313111225287703 113647978351969666837931555)
          ·
            refine ⟨170471967527954500256897333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113647978351969666837931555 170471967527954500256897333)
            ·
              refine ⟨15981746955745734399084125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170471967527954500256897333 15981746955745734399084125)
              ·
                refine ⟨5993155108404650399656547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15981746955745734399084125 5993155108404650399656547)
                ·
                  refine ⟨8989732662606975599484821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5993155108404650399656547 8989732662606975599484821)
                  ·
                    refine ⟨421393718559701981225851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8989732662606975599484821 421393718559701981225851)
                    ·
                      rfl

theorem cell22_1230992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_1230992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230992 prefixEnd_1230992 := by exact prefixLift 1230992
  have htrace : WordTrace (prefixWord ++ tailWord_1230992) baseStart_1230992 baseEnd_1230992 := by
    simpa [prefixWord, tailWord_1230992, baseEnd_1230992] using wordTrace_append hprefix tailTrace_1230992
  have hstable : (prefixWord ++ tailWord_1230992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230992).length < 2 ^ (prefixWord ++ tailWord_1230992).sum := by decide
  have hdescent : baseEnd_1230992 < baseStart_1230992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1230994 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1230994 : Nat := 118140960795 + 1230994 * 2 ^ 59
def prefixEnd_1230994 : Nat := 4983230072969 + 3 ^ 40 * 1230994 * 2
def baseEnd_1230994 : Nat := 421394403200574642675845

theorem tailTrace_1230994 : CollatzResearch.WordTrace tailWord_1230994 prefixEnd_1230994 421394403200574642675845 := by
  unfold tailWord_1230994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11224509925581612470621009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29932026468217633254989357 11224509925581612470621009)
  ·
    refine ⟨8418382444186209352965757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11224509925581612470621009 8418382444186209352965757)
    ·
      refine ⟨3156893416569828507362159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8418382444186209352965757 3156893416569828507362159)
      ·
        refine ⟨4735340124854742761043239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3156893416569828507362159 4735340124854742761043239)
        ·
          refine ⟨7103010187282114141564859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735340124854742761043239 7103010187282114141564859)
          ·
            refine ⟨10654515280923171212347289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7103010187282114141564859 10654515280923171212347289)
            ·
              refine ⟨7990886460692378409260467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10654515280923171212347289 7990886460692378409260467)
              ·
                refine ⟨11986329691038567613890701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7990886460692378409260467 11986329691038567613890701)
                ·
                  refine ⟨4494873634139462855209013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11986329691038567613890701 4494873634139462855209013)
                  ·
                    refine ⟨421394403200574642675845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4494873634139462855209013 421394403200574642675845)
                    ·
                      rfl

theorem cell22_1230994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1230994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1230994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1230994 prefixEnd_1230994 := by exact prefixLift 1230994
  have htrace : WordTrace (prefixWord ++ tailWord_1230994) baseStart_1230994 baseEnd_1230994 := by
    simpa [prefixWord, tailWord_1230994, baseEnd_1230994] using wordTrace_append hprefix tailTrace_1230994
  have hstable : (prefixWord ++ tailWord_1230994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1230994).length < 2 ^ (prefixWord ++ tailWord_1230994).sum := by decide
  have hdescent : baseEnd_1230994 < baseStart_1230994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1230994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231009 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1231009 : Nat := 118140960795 + 1231009 * 2 ^ 59
def prefixEnd_1231009 : Nat := 4983230072969 + 3 ^ 40 * 1231009 * 2
def baseEnd_1231009 : Nat := 421399538007119603550799

theorem tailTrace_1231009 : CollatzResearch.WordTrace tailWord_1231009 prefixEnd_1231009 421399538007119603550799 := by
  unfold tailWord_1231009
  simp only [CollatzResearch.WordTrace]
  refine ⟨44898586797272107444280081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29932391198181404962853387 44898586797272107444280081)
  ·
    refine ⟨33673940097954080583210061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44898586797272107444280081 33673940097954080583210061)
    ·
      refine ⟨12627727536732780218703773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33673940097954080583210061 12627727536732780218703773)
      ·
        refine ⟨4735397826274792582013915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12627727536732780218703773 4735397826274792582013915)
        ·
          refine ⟨7103096739412188873020873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735397826274792582013915 7103096739412188873020873)
          ·
            refine ⟨5327322554559141654765655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7103096739412188873020873 5327322554559141654765655)
            ·
              refine ⟨7990983831838712482148483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5327322554559141654765655 7990983831838712482148483)
              ·
                refine ⟨11986475747758068723222725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7990983831838712482148483 11986475747758068723222725)
                ·
                  refine ⟨2247464202704637885604261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11986475747758068723222725 2247464202704637885604261)
                  ·
                    refine ⟨421399538007119603550799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247464202704637885604261 421399538007119603550799)
                    ·
                      rfl

theorem cell22_1231009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1231009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231009 prefixEnd_1231009 := by exact prefixLift 1231009
  have htrace : WordTrace (prefixWord ++ tailWord_1231009) baseStart_1231009 baseEnd_1231009 := by
    simpa [prefixWord, tailWord_1231009, baseEnd_1231009] using wordTrace_append hprefix tailTrace_1231009
  have hstable : (prefixWord ++ tailWord_1231009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231009).length < 2 ^ (prefixWord ++ tailWord_1231009).sum := by decide
  have hdescent : baseEnd_1231009 < baseStart_1231009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231039 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 5, 3]
def baseStart_1231039 : Nat := 118140960795 + 1231039 * 2 ^ 59
def prefixEnd_1231039 : Nat := 4983230072969 + 3 ^ 40 * 1231039 * 2
def baseEnd_1231039 : Nat := 421409807620209525300707

theorem tailTrace_1231039 : CollatzResearch.WordTrace tailWord_1231039 prefixEnd_1231039 421409807620209525300707 := by
  unfold tailWord_1231039
  simp only [CollatzResearch.WordTrace]
  refine ⟨44899680987163422567872171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29933120658108948378581447 44899680987163422567872171)
  ·
    refine ⟨67349521480745133851808257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44899680987163422567872171 67349521480745133851808257)
    ·
      refine ⟨50512141110558850388856193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67349521480745133851808257 50512141110558850388856193)
      ·
        refine ⟨37884105832919137791642145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50512141110558850388856193 37884105832919137791642145)
        ·
          refine ⟨28413079374689353343731609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37884105832919137791642145 28413079374689353343731609)
          ·
            refine ⟨21309809531017015007798707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28413079374689353343731609 21309809531017015007798707)
            ·
              refine ⟨31964714296525522511698061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21309809531017015007798707 31964714296525522511698061)
              ·
                refine ⟨11986767861197070941886773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31964714296525522511698061 11986767861197070941886773)
                ·
                  refine ⟨1123759486987225400801885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11986767861197070941886773 1123759486987225400801885)
                  ·
                    refine ⟨421409807620209525300707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1123759486987225400801885 421409807620209525300707)
                    ·
                      rfl

theorem cell22_1231039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_1231039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231039 prefixEnd_1231039 := by exact prefixLift 1231039
  have htrace : WordTrace (prefixWord ++ tailWord_1231039) baseStart_1231039 baseEnd_1231039 := by
    simpa [prefixWord, tailWord_1231039, baseEnd_1231039] using wordTrace_append hprefix tailTrace_1231039
  have hstable : (prefixWord ++ tailWord_1231039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231039).length < 2 ^ (prefixWord ++ tailWord_1231039).sum := by decide
  have hdescent : baseEnd_1231039 < baseStart_1231039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231073 : List Nat := [1, 2, 3, 1, 3, 1, 3, 4, 1, 3]
def baseStart_1231073 : Nat := 118140960795 + 1231073 * 2 ^ 59
def prefixEnd_1231073 : Nat := 4983230072969 + 3 ^ 40 * 1231073 * 2
def baseEnd_1231073 : Nat := 421421446515044769950603

theorem tailTrace_1231073 : CollatzResearch.WordTrace tailWord_1231073 prefixEnd_1231073 421421446515044769950603 := by
  unfold tailWord_1231073
  simp only [CollatzResearch.WordTrace]
  refine ⟨44900921069040246374609873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29933947379360164249739915 44900921069040246374609873)
  ·
    refine ⟨33675690801780184780957405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44900921069040246374609873 33675690801780184780957405)
    ·
      refine ⟨12628384050667569292859027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33675690801780184780957405 12628384050667569292859027)
      ·
        refine ⟨18942576076001353939288541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12628384050667569292859027 18942576076001353939288541)
        ·
          refine ⟨7103466028500507727233203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18942576076001353939288541 7103466028500507727233203)
          ·
            refine ⟨10655199042750761590849805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7103466028500507727233203 10655199042750761590849805)
            ·
              refine ⟨3995699641031535596568677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10655199042750761590849805 3995699641031535596568677)
              ·
                refine ⟨749193682693412924356627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3995699641031535596568677 749193682693412924356627)
                ·
                  refine ⟨1123790524040119386534941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749193682693412924356627 1123790524040119386534941)
                  ·
                    refine ⟨421421446515044769950603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1123790524040119386534941 421421446515044769950603)
                    ·
                      rfl

theorem cell22_1231073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_1231073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231073 prefixEnd_1231073 := by exact prefixLift 1231073
  have htrace : WordTrace (prefixWord ++ tailWord_1231073) baseStart_1231073 baseEnd_1231073 := by
    simpa [prefixWord, tailWord_1231073, baseEnd_1231073] using wordTrace_append hprefix tailTrace_1231073
  have hstable : (prefixWord ++ tailWord_1231073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231073).length < 2 ^ (prefixWord ++ tailWord_1231073).sum := by decide
  have hdescent : baseEnd_1231073 < baseStart_1231073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231084 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_1231084 : Nat := 118140960795 + 1231084 * 2 ^ 59
def prefixEnd_1231084 : Nat := 4983230072969 + 3 ^ 40 * 1231084 * 2
def baseEnd_1231084 : Nat := 421425212039844407925569

theorem tailTrace_1231084 : CollatzResearch.WordTrace tailWord_1231084 prefixEnd_1231084 421425212039844407925569 := by
  unfold tailWord_1231084
  simp only [CollatzResearch.WordTrace]
  refine ⟨22450661136000197626630153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29934214848000263502173537 22450661136000197626630153)
  ·
    refine ⟨16837995852000148219972615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22450661136000197626630153 16837995852000148219972615)
    ·
      refine ⟨25256993778000222329958923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16837995852000148219972615 25256993778000222329958923)
      ·
        refine ⟨37885490667000333494938385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25256993778000222329958923 37885490667000333494938385)
        ·
          refine ⟨28414118000250250121203789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37885490667000333494938385 28414118000250250121203789)
          ·
            refine ⟨10655294250093843795451421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28414118000250250121203789 10655294250093843795451421)
            ·
              refine ⟨3995735343785191423294283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10655294250093843795451421 3995735343785191423294283)
              ·
                refine ⟨5993603015677787134941425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3995735343785191423294283 5993603015677787134941425)
                ·
                  refine ⟨4495202261758340351206069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5993603015677787134941425 4495202261758340351206069)
                  ·
                    refine ⟨421425212039844407925569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4495202261758340351206069 421425212039844407925569)
                    ·
                      rfl

theorem cell22_1231084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_1231084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231084 prefixEnd_1231084 := by exact prefixLift 1231084
  have htrace : WordTrace (prefixWord ++ tailWord_1231084) baseStart_1231084 baseEnd_1231084 := by
    simpa [prefixWord, tailWord_1231084, baseEnd_1231084] using wordTrace_append hprefix tailTrace_1231084
  have hstable : (prefixWord ++ tailWord_1231084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231084).length < 2 ^ (prefixWord ++ tailWord_1231084).sum := by decide
  have hdescent : baseEnd_1231084 < baseStart_1231084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231116 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_1231116 : Nat := 118140960795 + 1231116 * 2 ^ 59
def prefixEnd_1231116 : Nat := 4983230072969 + 3 ^ 40 * 1231116 * 2
def baseEnd_1231116 : Nat := 421436166293806991125471

theorem tailTrace_1231116 : CollatzResearch.WordTrace tailWord_1231116 prefixEnd_1231116 421436166293806991125471 := by
  unfold tailWord_1231116
  simp only [CollatzResearch.WordTrace]
  refine ⟨22451244703942232359212601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29934992938589643145616801 22451244703942232359212601)
  ·
    refine ⟨16838433527956674269409451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22451244703942232359212601 16838433527956674269409451)
    ·
      refine ⟨25257650291935011404114177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16838433527956674269409451 25257650291935011404114177)
      ·
        refine ⟨18943237718951258553085633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25257650291935011404114177 18943237718951258553085633)
        ·
          refine ⟨14207428289213443914814225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18943237718951258553085633 14207428289213443914814225)
          ·
            refine ⟨10655571216910082936110669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14207428289213443914814225 10655571216910082936110669)
            ·
              refine ⟨3995839206341281101041501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10655571216910082936110669 3995839206341281101041501)
              ·
                refine ⟨1498439702377980412890563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3995839206341281101041501 1498439702377980412890563)
                ·
                  refine ⟨2247659553566970619335845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498439702377980412890563 2247659553566970619335845)
                  ·
                    refine ⟨421436166293806991125471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247659553566970619335845 421436166293806991125471)
                    ·
                      rfl

theorem cell22_1231116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_1231116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231116 prefixEnd_1231116 := by exact prefixLift 1231116
  have htrace : WordTrace (prefixWord ++ tailWord_1231116) baseStart_1231116 baseEnd_1231116 := by
    simpa [prefixWord, tailWord_1231116, baseEnd_1231116] using wordTrace_append hprefix tailTrace_1231116
  have hstable : (prefixWord ++ tailWord_1231116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231116).length < 2 ^ (prefixWord ++ tailWord_1231116).sum := by decide
  have hdescent : baseEnd_1231116 < baseStart_1231116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231131 : List Nat := [1, 1, 1, 1, 1, 1, 8, 4, 4]
def baseStart_1231131 : Nat := 118140960795 + 1231131 * 2 ^ 59
def prefixEnd_1231131 : Nat := 4983230072969 + 3 ^ 40 * 1231131 * 2
def baseEnd_1231131 : Nat := 140480433700117317333475

theorem tailTrace_1231131 : CollatzResearch.WordTrace tailWord_1231131 prefixEnd_1231131 140480433700117317333475 := by
  unfold tailWord_1231131
  simp only [CollatzResearch.WordTrace]
  refine ⟨44903036502830122280221247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29935357668553414853480831 44903036502830122280221247)
  ·
    refine ⟨67354554754245183420331871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44903036502830122280221247 67354554754245183420331871)
    ·
      refine ⟨101031832131367775130497807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67354554754245183420331871 101031832131367775130497807)
      ·
        refine ⟨151547748197051662695746711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101031832131367775130497807 151547748197051662695746711)
        ·
          refine ⟨227321622295577494043620067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151547748197051662695746711 227321622295577494043620067)
          ·
            refine ⟨340982433443366241065430101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227321622295577494043620067 340982433443366241065430101)
            ·
              refine ⟨3995887891914448137485509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 340982433443366241065430101 3995887891914448137485509)
              ·
                refine ⟨749228979733959025778533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3995887891914448137485509 749228979733959025778533)
                ·
                  refine ⟨140480433700117317333475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749228979733959025778533 140480433700117317333475)
                  ·
                    rfl

theorem cell22_1231131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 4].length) (baseStart_1231131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231131 prefixEnd_1231131 := by exact prefixLift 1231131
  have htrace : WordTrace (prefixWord ++ tailWord_1231131) baseStart_1231131 baseEnd_1231131 := by
    simpa [prefixWord, tailWord_1231131, baseEnd_1231131] using wordTrace_append hprefix tailTrace_1231131
  have hstable : (prefixWord ++ tailWord_1231131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231131).length < 2 ^ (prefixWord ++ tailWord_1231131).sum := by decide
  have hdescent : baseEnd_1231131 < baseStart_1231131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231161 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_1231161 : Nat := 118140960795 + 1231161 * 2 ^ 59
def prefixEnd_1231161 : Nat := 4983230072969 + 3 ^ 40 * 1231161 * 2
def baseEnd_1231161 : Nat := 421451570713441873750333

theorem tailTrace_1231161 : CollatzResearch.WordTrace tailWord_1231161 prefixEnd_1231161 421451570713441873750333 := by
  unfold tailWord_1231161
  simp only [CollatzResearch.WordTrace]
  refine ⟨44904130692721437403813337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29936087128480958269208891 44904130692721437403813337)
  ·
    refine ⟨33678098019541078052860003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44904130692721437403813337 33678098019541078052860003)
    ·
      refine ⟨50517147029311617079290005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33678098019541078052860003 50517147029311617079290005)
      ·
        refine ⟨2367991266998982050591719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50517147029311617079290005 2367991266998982050591719)
        ·
          refine ⟨3551986900498473075887579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367991266998982050591719 3551986900498473075887579)
          ·
            refine ⟨5327980350747709613831369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551986900498473075887579 5327980350747709613831369)
            ·
              refine ⟨3995985263060782210373527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5327980350747709613831369 3995985263060782210373527)
              ·
                refine ⟨5993977894591173315560291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3995985263060782210373527 5993977894591173315560291)
                ·
                  refine ⟨8990966841886759973340437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5993977894591173315560291 8990966841886759973340437)
                  ·
                    refine ⟨421451570713441873750333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8990966841886759973340437 421451570713441873750333)
                    ·
                      rfl

theorem cell22_1231161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_1231161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231161 prefixEnd_1231161 := by exact prefixLift 1231161
  have htrace : WordTrace (prefixWord ++ tailWord_1231161) baseStart_1231161 baseEnd_1231161 := by
    simpa [prefixWord, tailWord_1231161, baseEnd_1231161] using wordTrace_append hprefix tailTrace_1231161
  have hstable : (prefixWord ++ tailWord_1231161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231161).length < 2 ^ (prefixWord ++ tailWord_1231161).sum := by decide
  have hdescent : baseEnd_1231161 < baseStart_1231161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231219 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 1, 7]
def baseStart_1231219 : Nat := 118140960795 + 1231219 * 2 ^ 59
def prefixEnd_1231219 : Nat := 4983230072969 + 3 ^ 40 * 1231219 * 2
def baseEnd_1231219 : Nat := 421471425298749055800155

theorem tailTrace_1231219 : CollatzResearch.WordTrace tailWord_1231219 prefixEnd_1231219 421471425298749055800155 := by
  unfold tailWord_1231219
  simp only [CollatzResearch.WordTrace]
  refine ⟨44906246126511313309424711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29937497417674208872949807 44906246126511313309424711)
  ·
    refine ⟨67359369189766969964137067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44906246126511313309424711 67359369189766969964137067)
    ·
      refine ⟨101039053784650454946205601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67359369189766969964137067 101039053784650454946205601)
      ·
        refine ⟨75779290338487841209654201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101039053784650454946205601 75779290338487841209654201)
        ·
          refine ⟨56834467753865880907240651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75779290338487841209654201 56834467753865880907240651)
          ·
            refine ⟨85251701630798821360860977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56834467753865880907240651 85251701630798821360860977)
            ·
              refine ⟨63938776223099116020645733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85251701630798821360860977 63938776223099116020645733)
              ·
                refine ⟨11988520541831084253871075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63938776223099116020645733 11988520541831084253871075)
                ·
                  refine ⟨17982780812746626380806613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11988520541831084253871075 17982780812746626380806613)
                  ·
                    refine ⟨421471425298749055800155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17982780812746626380806613 421471425298749055800155)
                    ·
                      rfl

theorem cell22_1231219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_1231219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231219 prefixEnd_1231219 := by exact prefixLift 1231219
  have htrace : WordTrace (prefixWord ++ tailWord_1231219) baseStart_1231219 baseEnd_1231219 := by
    simpa [prefixWord, tailWord_1231219, baseEnd_1231219] using wordTrace_append hprefix tailTrace_1231219
  have hstable : (prefixWord ++ tailWord_1231219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231219).length < 2 ^ (prefixWord ++ tailWord_1231219).sum := by decide
  have hdescent : baseEnd_1231219 < baseStart_1231219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231236 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1231236 : Nat := 118140960795 + 1231236 * 2 ^ 59
def prefixEnd_1231236 : Nat := 4983230072969 + 3 ^ 40 * 1231236 * 2
def baseEnd_1231236 : Nat := 421477244746166678125103

theorem tailTrace_1231236 : CollatzResearch.WordTrace tailWord_1231236 prefixEnd_1231236 421477244746166678125103 := by
  unfold tailWord_1231236
  simp only [CollatzResearch.WordTrace]
  refine ⟨22453433083724862606396781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29937910778299816808529041 22453433083724862606396781)
  ·
    refine ⟨8420037406396823477398793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22453433083724862606396781 8420037406396823477398793)
    ·
      refine ⟨6315028054797617608049095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8420037406396823477398793 6315028054797617608049095)
      ·
        refine ⟨9472542082196426412073643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315028054797617608049095 9472542082196426412073643)
        ·
          refine ⟨14208813123294639618110465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9472542082196426412073643 14208813123294639618110465)
          ·
            refine ⟨10656609842470979713582849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14208813123294639618110465 10656609842470979713582849)
            ·
              refine ⟨7992457381853234785187137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10656609842470979713582849 7992457381853234785187137)
              ·
                refine ⟨5994343036389926088890353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7992457381853234785187137 5994343036389926088890353)
                ·
                  refine ⟨4495757277292444566667765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5994343036389926088890353 4495757277292444566667765)
                  ·
                    refine ⟨421477244746166678125103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4495757277292444566667765 421477244746166678125103)
                    ·
                      rfl

theorem cell22_1231236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1231236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231236 prefixEnd_1231236 := by exact prefixLift 1231236
  have htrace : WordTrace (prefixWord ++ tailWord_1231236) baseStart_1231236 baseEnd_1231236 := by
    simpa [prefixWord, tailWord_1231236, baseEnd_1231236] using wordTrace_append hprefix tailTrace_1231236
  have hstable : (prefixWord ++ tailWord_1231236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231236).length < 2 ^ (prefixWord ++ tailWord_1231236).sum := by decide
  have hdescent : baseEnd_1231236 < baseStart_1231236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231285 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1231285 : Nat := 118140960795 + 1231285 * 2 ^ 59
def prefixEnd_1231285 : Nat := 4983230072969 + 3 ^ 40 * 1231285 * 2
def baseEnd_1231285 : Nat := 421494018447546883649953

theorem tailTrace_1231285 : CollatzResearch.WordTrace tailWord_1231285 prefixEnd_1231285 421494018447546883649953 := by
  unfold tailWord_1231285
  simp only [CollatzResearch.WordTrace]
  refine ⟨44908653344272206581327309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29939102229514804387551539 44908653344272206581327309)
  ·
    refine ⟨16840745004102077467997741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44908653344272206581327309 16840745004102077467997741)
    ·
      refine ⟨6315279376538279050499153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16840745004102077467997741 6315279376538279050499153)
      ·
        refine ⟨4736459532403709287874365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6315279376538279050499153 4736459532403709287874365)
        ·
          refine ⟨1776172324651390982952887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4736459532403709287874365 1776172324651390982952887)
          ·
            refine ⟨2664258486977086474429331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776172324651390982952887 2664258486977086474429331)
            ·
              refine ⟨3996387730465629711643997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664258486977086474429331 3996387730465629711643997)
              ·
                refine ⟨1498645398924611141866499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3996387730465629711643997 1498645398924611141866499)
                ·
                  refine ⟨2247968098386916712799749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498645398924611141866499 2247968098386916712799749)
                  ·
                    refine ⟨421494018447546883649953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247968098386916712799749 421494018447546883649953)
                    ·
                      rfl

theorem cell22_1231285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1231285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231285 prefixEnd_1231285 := by exact prefixLift 1231285
  have htrace : WordTrace (prefixWord ++ tailWord_1231285) baseStart_1231285 baseEnd_1231285 := by
    simpa [prefixWord, tailWord_1231285, baseEnd_1231285] using wordTrace_append hprefix tailTrace_1231285
  have hstable : (prefixWord ++ tailWord_1231285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231285).length < 2 ^ (prefixWord ++ tailWord_1231285).sum := by decide
  have hdescent : baseEnd_1231285 < baseStart_1231285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231296 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_1231296 : Nat := 118140960795 + 1231296 * 2 ^ 59
def prefixEnd_1231296 : Nat := 4983230072969 + 3 ^ 40 * 1231296 * 2
def baseEnd_1231296 : Nat := 421497783972346521624919

theorem tailTrace_1231296 : CollatzResearch.WordTrace tailWord_1231296 prefixEnd_1231296 421497783972346521624919 := by
  unfold tailWord_1231296
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454527273616177729988871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29939369698154903639985161 22454527273616177729988871)
  ·
    refine ⟨33681790910424266594983307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22454527273616177729988871 33681790910424266594983307)
    ·
      refine ⟨50522686365636399892474961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33681790910424266594983307 50522686365636399892474961)
      ·
        refine ⟨37892014774227299919356221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50522686365636399892474961 37892014774227299919356221)
        ·
          refine ⟨14209505540335237469758583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37892014774227299919356221 14209505540335237469758583)
          ·
            refine ⟨21314258310502856204637875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14209505540335237469758583 21314258310502856204637875)
            ·
              refine ⟨31971387465754284306956813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21314258310502856204637875 31971387465754284306956813)
              ·
                refine ⟨11989270299657856615108805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31971387465754284306956813 11989270299657856615108805)
                ·
                  refine ⟨2247988181185848115332901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11989270299657856615108805 2247988181185848115332901)
                  ·
                    refine ⟨421497783972346521624919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2247988181185848115332901 421497783972346521624919)
                    ·
                      rfl

theorem cell22_1231296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_1231296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231296 prefixEnd_1231296 := by exact prefixLift 1231296
  have htrace : WordTrace (prefixWord ++ tailWord_1231296) baseStart_1231296 baseEnd_1231296 := by
    simpa [prefixWord, tailWord_1231296, baseEnd_1231296] using wordTrace_append hprefix tailTrace_1231296
  have hstable : (prefixWord ++ tailWord_1231296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231296).length < 2 ^ (prefixWord ++ tailWord_1231296).sum := by decide
  have hdescent : baseEnd_1231296 < baseStart_1231296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231300 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 6]
def baseStart_1231300 : Nat := 118140960795 + 1231300 * 2 ^ 59
def prefixEnd_1231300 : Nat := 4983230072969 + 3 ^ 40 * 1231300 * 2
def baseEnd_1231300 : Nat := 140499717751363948174969

theorem tailTrace_1231300 : CollatzResearch.WordTrace tailWord_1231300 prefixEnd_1231300 140499717751363948174969 := by
  unfold tailWord_1231300
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454600219608932071561677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29939466959478576095415569 22454600219608932071561677)
  ·
    refine ⟨8420475082353349526835629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22454600219608932071561677 8420475082353349526835629)
    ·
      refine ⟨3157678155882506072563361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8420475082353349526835629 3157678155882506072563361)
      ·
        refine ⟨2368258616911879554422521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3157678155882506072563361 2368258616911879554422521)
        ·
          refine ⟨1776193962683909665816891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2368258616911879554422521 1776193962683909665816891)
          ·
            refine ⟨2664290944025864498725337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776193962683909665816891 2664290944025864498725337)
            ·
              refine ⟨1998218208019398374044003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664290944025864498725337 1998218208019398374044003)
              ·
                refine ⟨2997327312029097561066005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998218208019398374044003 2997327312029097561066005)
                ·
                  refine ⟨140499717751363948174969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2997327312029097561066005 140499717751363948174969)
                  ·
                    rfl

theorem cell22_1231300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_1231300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231300 prefixEnd_1231300 := by exact prefixLift 1231300
  have htrace : WordTrace (prefixWord ++ tailWord_1231300) baseStart_1231300 baseEnd_1231300 := by
    simpa [prefixWord, tailWord_1231300, baseEnd_1231300] using wordTrace_append hprefix tailTrace_1231300
  have hstable : (prefixWord ++ tailWord_1231300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231300).length < 2 ^ (prefixWord ++ tailWord_1231300).sum := by decide
  have hdescent : baseEnd_1231300 < baseStart_1231300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231366 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1231366 : Nat := 118140960795 + 1231366 * 2 ^ 59
def prefixEnd_1231366 : Nat := 4983230072969 + 3 ^ 40 * 1231366 * 2
def baseEnd_1231366 : Nat := 421521746402889672374705

theorem tailTrace_1231366 : CollatzResearch.WordTrace tailWord_1231366 prefixEnd_1231366 421521746402889672374705 := by
  unfold tailWord_1231366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403487739280586169219561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29941071771319171610017301 1403487739280586169219561)
  ·
    refine ⟨1052615804460439626914671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1403487739280586169219561 1052615804460439626914671)
    ·
      refine ⟨1578923706690659440372007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1052615804460439626914671 1578923706690659440372007)
      ·
        refine ⟨2368385560035989160558011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578923706690659440372007 2368385560035989160558011)
        ·
          refine ⟨3552578340053983740837017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368385560035989160558011 3552578340053983740837017)
          ·
            refine ⟨2664433755040487805627763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3552578340053983740837017 2664433755040487805627763)
            ·
              refine ⟨3996650632560731708441645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664433755040487805627763 3996650632560731708441645)
              ·
                refine ⟨1498743987210274390665617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3996650632560731708441645 1498743987210274390665617)
                ·
                  refine ⟨1124057990407705792999213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1498743987210274390665617 1124057990407705792999213)
                  ·
                    refine ⟨421521746402889672374705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124057990407705792999213 421521746402889672374705)
                    ·
                      rfl

theorem cell22_1231366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1231366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231366 prefixEnd_1231366 := by exact prefixLift 1231366
  have htrace : WordTrace (prefixWord ++ tailWord_1231366) baseStart_1231366 baseEnd_1231366 := by
    simpa [prefixWord, tailWord_1231366, baseEnd_1231366] using wordTrace_append hprefix tailTrace_1231366
  have hstable : (prefixWord ++ tailWord_1231366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231366).length < 2 ^ (prefixWord ++ tailWord_1231366).sum := by decide
  have hdescent : baseEnd_1231366 < baseStart_1231366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231403 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 1, 4]
def baseStart_1231403 : Nat := 118140960795 + 1231403 * 2 ^ 59
def prefixEnd_1231403 : Nat := 4983230072969 + 3 ^ 40 * 1231403 * 2
def baseEnd_1231403 : Nat := 421534412259033909199591

theorem tailTrace_1231403 : CollatzResearch.WordTrace tailWord_1231403 prefixEnd_1231403 421534412259033909199591 := by
  unfold tailWord_1231403
  simp only [CollatzResearch.WordTrace]
  refine ⟨44912957157844712734122863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29941971438563141822748575 44912957157844712734122863)
  ·
    refine ⟨67369435736767069101184295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44912957157844712734122863 67369435736767069101184295)
    ·
      refine ⟨101054153605150603651776443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67369435736767069101184295 101054153605150603651776443)
      ·
        refine ⟨151581230407725905477664665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101054153605150603651776443 151581230407725905477664665)
        ·
          refine ⟨113685922805794429108248499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151581230407725905477664665 113685922805794429108248499)
          ·
            refine ⟨170528884208691643662372749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113685922805794429108248499 170528884208691643662372749)
            ·
              refine ⟨63948331578259366373389781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170528884208691643662372749 63948331578259366373389781)
              ·
                refine ⟨1498789021365453899376323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63948331578259366373389781 1498789021365453899376323)
                ·
                  refine ⟨2248183532048180849064485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498789021365453899376323 2248183532048180849064485)
                  ·
                    refine ⟨421534412259033909199591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2248183532048180849064485 421534412259033909199591)
                    ·
                      rfl

theorem cell22_1231403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 4].length) (baseStart_1231403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231403 prefixEnd_1231403 := by exact prefixLift 1231403
  have htrace : WordTrace (prefixWord ++ tailWord_1231403) baseStart_1231403 baseEnd_1231403 := by
    simpa [prefixWord, tailWord_1231403, baseEnd_1231403] using wordTrace_append hprefix tailTrace_1231403
  have hstable : (prefixWord ++ tailWord_1231403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231403).length < 2 ^ (prefixWord ++ tailWord_1231403).sum := by decide
  have hdescent : baseEnd_1231403 < baseStart_1231403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231422 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_1231422 : Nat := 118140960795 + 1231422 * 2 ^ 59
def prefixEnd_1231422 : Nat := 4983230072969 + 3 ^ 40 * 1231422 * 2
def baseEnd_1231422 : Nat := 421540916347324192974533

theorem tailTrace_1231422 : CollatzResearch.WordTrace tailWord_1231422 prefixEnd_1231422 421540916347324192974533 := by
  unfold tailWord_1231422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5614206268096984872383065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29942433429850585986043013 5614206268096984872383065)
  ·
    refine ⟨4210654701072738654287299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5614206268096984872383065 4210654701072738654287299)
    ·
      refine ⟨6315982051609107981430949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4210654701072738654287299 6315982051609107981430949)
      ·
        refine ⟨1184246634676707746518303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6315982051609107981430949 1184246634676707746518303)
        ·
          refine ⟨1776369952015061619777455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184246634676707746518303 1776369952015061619777455)
          ·
            refine ⟨2664554928022592429666183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776369952015061619777455 2664554928022592429666183)
            ·
              refine ⟨3996832392033888644499275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664554928022592429666183 3996832392033888644499275)
              ·
                refine ⟨5995248588050832966748913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3996832392033888644499275 5995248588050832966748913)
                ·
                  refine ⟨4496436441038124725061685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5995248588050832966748913 4496436441038124725061685)
                  ·
                    refine ⟨421540916347324192974533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4496436441038124725061685 421540916347324192974533)
                    ·
                      rfl

theorem cell22_1231422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_1231422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231422 prefixEnd_1231422 := by exact prefixLift 1231422
  have htrace : WordTrace (prefixWord ++ tailWord_1231422) baseStart_1231422 baseEnd_1231422 := by
    simpa [prefixWord, tailWord_1231422, baseEnd_1231422] using wordTrace_append hprefix tailTrace_1231422
  have hstable : (prefixWord ++ tailWord_1231422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231422).length < 2 ^ (prefixWord ++ tailWord_1231422).sum := by decide
  have hdescent : baseEnd_1231422 < baseStart_1231422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231433 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 8, 3]
def baseStart_1231433 : Nat := 118140960795 + 1231433 * 2 ^ 59
def prefixEnd_1231433 : Nat := 4983230072969 + 3 ^ 40 * 1231433 * 2
def baseEnd_1231433 : Nat := 421544681872123830949499

theorem tailTrace_1231433 : CollatzResearch.WordTrace tailWord_1231433 prefixEnd_1231433 421544681872123830949499 := by
  unfold tailWord_1231433
  simp only [CollatzResearch.WordTrace]
  refine ⟨44914051347736027857714953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29942700898490685238476635 44914051347736027857714953)
  ·
    refine ⟨33685538510802020893286215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44914051347736027857714953 33685538510802020893286215)
    ·
      refine ⟨50528307766203031339929323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33685538510802020893286215 50528307766203031339929323)
      ·
        refine ⟨75792461649304547009893985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50528307766203031339929323 75792461649304547009893985)
        ·
          refine ⟨56844346236978410257420489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75792461649304547009893985 56844346236978410257420489)
          ·
            refine ⟨42633259677733807693065367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56844346236978410257420489 42633259677733807693065367)
            ·
              refine ⟨63949889516600711539598051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42633259677733807693065367 63949889516600711539598051)
              ·
                refine ⟨95924834274901067309397077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63949889516600711539598051 95924834274901067309397077)
                ·
                  refine ⟨1124119151658996882531997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 95924834274901067309397077 1124119151658996882531997)
                  ·
                    refine ⟨421544681872123830949499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124119151658996882531997 421544681872123830949499)
                    ·
                      rfl

theorem cell22_1231433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_1231433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231433 prefixEnd_1231433 := by exact prefixLift 1231433
  have htrace : WordTrace (prefixWord ++ tailWord_1231433) baseStart_1231433 baseEnd_1231433 := by
    simpa [prefixWord, tailWord_1231433, baseEnd_1231433] using wordTrace_append hprefix tailTrace_1231433
  have hstable : (prefixWord ++ tailWord_1231433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231433).length < 2 ^ (prefixWord ++ tailWord_1231433).sum := by decide
  have hdescent : baseEnd_1231433 < baseStart_1231433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231495 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1231495 : Nat := 118140960795 + 1231495 * 2 ^ 59
def prefixEnd_1231495 : Nat := 4983230072969 + 3 ^ 40 * 1231495 * 2
def baseEnd_1231495 : Nat := 421565905739176335899309

theorem tailTrace_1231495 : CollatzResearch.WordTrace tailWord_1231495 prefixEnd_1231495 421565905739176335899309 := by
  unfold tailWord_1231495
  simp only [CollatzResearch.WordTrace]
  refine ⟨44916312673511412446471939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29944208449007608297647959 44916312673511412446471939)
  ·
    refine ⟨67374469010267118669707909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44916312673511412446471939 67374469010267118669707909)
    ·
      refine ⟨12632712939425084750570233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67374469010267118669707909 12632712939425084750570233)
      ·
        refine ⟨9474534704568813562927675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12632712939425084750570233 9474534704568813562927675)
        ·
          refine ⟨14211802056853220344391513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9474534704568813562927675 14211802056853220344391513)
          ·
            refine ⟨10658851542639915258293635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14211802056853220344391513 10658851542639915258293635)
            ·
              refine ⟨15988277313959872887440453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10658851542639915258293635 15988277313959872887440453)
              ·
                refine ⟨2997801996367476166395085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15988277313959872887440453 2997801996367476166395085)
                ·
                  refine ⟨1124175748637803562398157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2997801996367476166395085 1124175748637803562398157)
                  ·
                    refine ⟨421565905739176335899309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124175748637803562398157 421565905739176335899309)
                    ·
                      rfl

theorem cell22_1231495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1231495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231495 prefixEnd_1231495 := by exact prefixLift 1231495
  have htrace : WordTrace (prefixWord ++ tailWord_1231495) baseStart_1231495 baseEnd_1231495 := by
    simpa [prefixWord, tailWord_1231495, baseEnd_1231495] using wordTrace_append hprefix tailTrace_1231495
  have hstable : (prefixWord ++ tailWord_1231495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231495).length < 2 ^ (prefixWord ++ tailWord_1231495).sum := by decide
  have hdescent : baseEnd_1231495 < baseStart_1231495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231523 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 2, 5]
def baseStart_1231523 : Nat := 118140960795 + 1231523 * 2 ^ 59
def prefixEnd_1231523 : Nat := 4983230072969 + 3 ^ 40 * 1231523 * 2
def baseEnd_1231523 : Nat := 421575490711393596199223

theorem tailTrace_1231523 : CollatzResearch.WordTrace tailWord_1231523 prefixEnd_1231523 421575490711393596199223 := by
  unfold tailWord_1231523
  simp only [CollatzResearch.WordTrace]
  refine ⟨44917333917409973228491223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29944889278273315485660815 44917333917409973228491223)
  ·
    refine ⟨67376000876114959842736835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44917333917409973228491223 67376000876114959842736835)
    ·
      refine ⟨101064001314172439764105253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67376000876114959842736835 101064001314172439764105253)
      ·
        refine ⟨18949500246407332455769735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101064001314172439764105253 18949500246407332455769735)
        ·
          refine ⟨28424250369610998683654603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18949500246407332455769735 28424250369610998683654603)
          ·
            refine ⟨42636375554416498025481905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28424250369610998683654603 42636375554416498025481905)
            ·
              refine ⟨31977281665812373519111429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42636375554416498025481905 31977281665812373519111429)
              ·
                refine ⟨5995740312339820034833393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31977281665812373519111429 5995740312339820034833393)
                ·
                  refine ⟨4496805234254865026125045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5995740312339820034833393 4496805234254865026125045)
                  ·
                    refine ⟨421575490711393596199223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4496805234254865026125045 421575490711393596199223)
                    ·
                      rfl

theorem cell22_1231523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_1231523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231523 prefixEnd_1231523 := by exact prefixLift 1231523
  have htrace : WordTrace (prefixWord ++ tailWord_1231523) baseStart_1231523 baseEnd_1231523 := by
    simpa [prefixWord, tailWord_1231523, baseEnd_1231523] using wordTrace_append hprefix tailTrace_1231523
  have hstable : (prefixWord ++ tailWord_1231523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231523).length < 2 ^ (prefixWord ++ tailWord_1231523).sum := by decide
  have hdescent : baseEnd_1231523 < baseStart_1231523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231538 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1231538 : Nat := 118140960795 + 1231538 * 2 ^ 59
def prefixEnd_1231538 : Nat := 4983230072969 + 3 ^ 40 * 1231538 * 2
def baseEnd_1231538 : Nat := 421580625517938557074177

theorem tailTrace_1231538 : CollatzResearch.WordTrace tailWord_1231538 prefixEnd_1231538 421580625517938557074177 := by
  unfold tailWord_1231538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11229470253088907697571817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29945254008237087193524845 11229470253088907697571817)
  ·
    refine ⟨8422102689816680773178863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11229470253088907697571817 8422102689816680773178863)
    ·
      refine ⟨12633154034725021159768295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8422102689816680773178863 12633154034725021159768295)
      ·
        refine ⟨18949731052087531739652443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12633154034725021159768295 18949731052087531739652443)
        ·
          refine ⟨28424596578131297609478665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18949731052087531739652443 28424596578131297609478665)
          ·
            refine ⟨21318447433598473207108999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28424596578131297609478665 21318447433598473207108999)
            ·
              refine ⟨31977671150397709810663499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21318447433598473207108999 31977671150397709810663499)
              ·
                refine ⟨47966506725596564715995249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31977671150397709810663499 47966506725596564715995249)
                ·
                  refine ⟨35974880044197423536996437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47966506725596564715995249 35974880044197423536996437)
                  ·
                    refine ⟨421580625517938557074177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35974880044197423536996437 421580625517938557074177)
                    ·
                      rfl

theorem cell22_1231538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1231538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231538 prefixEnd_1231538 := by exact prefixLift 1231538
  have htrace : WordTrace (prefixWord ++ tailWord_1231538) baseStart_1231538 baseEnd_1231538 := by
    simpa [prefixWord, tailWord_1231538, baseEnd_1231538] using wordTrace_append hprefix tailTrace_1231538
  have hstable : (prefixWord ++ tailWord_1231538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231538).length < 2 ^ (prefixWord ++ tailWord_1231538).sum := by decide
  have hdescent : baseEnd_1231538 < baseStart_1231538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231602 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1231602 : Nat := 118140960795 + 1231602 * 2 ^ 59
def prefixEnd_1231602 : Nat := 4983230072969 + 3 ^ 40 * 1231602 * 2
def baseEnd_1231602 : Nat := 421602534025863723473981

theorem tailTrace_1231602 : CollatzResearch.WordTrace tailWord_1231602 prefixEnd_1231602 421602534025863723473981 := by
  unfold tailWord_1231602
  simp only [CollatzResearch.WordTrace]
  refine ⟨11230053821030942430154265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29946810189415846480411373 11230053821030942430154265)
  ·
    refine ⟨8422540365773206822615699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11230053821030942430154265 8422540365773206822615699)
    ·
      refine ⟨12633810548659810233923549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8422540365773206822615699 12633810548659810233923549)
      ·
        refine ⟨4737678955747428837721331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12633810548659810233923549 4737678955747428837721331)
        ·
          refine ⟨7106518433621143256581997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4737678955747428837721331 7106518433621143256581997)
          ·
            refine ⟨2664944412607928721218249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7106518433621143256581997 2664944412607928721218249)
            ·
              refine ⟨1998708309455946540913687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664944412607928721218249 1998708309455946540913687)
              ·
                refine ⟨2998062464183919811370531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998708309455946540913687 2998062464183919811370531)
                ·
                  refine ⟨4497093696275879717055797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998062464183919811370531 4497093696275879717055797)
                  ·
                    refine ⟨421602534025863723473981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4497093696275879717055797 421602534025863723473981)
                    ·
                      rfl

theorem cell22_1231602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1231602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231602 prefixEnd_1231602 := by exact prefixLift 1231602
  have htrace : WordTrace (prefixWord ++ tailWord_1231602) baseStart_1231602 baseEnd_1231602 := by
    simpa [prefixWord, tailWord_1231602, baseEnd_1231602] using wordTrace_append hprefix tailTrace_1231602
  have hstable : (prefixWord ++ tailWord_1231602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231602).length < 2 ^ (prefixWord ++ tailWord_1231602).sum := by decide
  have hdescent : baseEnd_1231602 < baseStart_1231602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231647 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 3, 3]
def baseStart_1231647 : Nat := 118140960795 + 1231647 * 2 ^ 59
def prefixEnd_1231647 : Nat := 4983230072969 + 3 ^ 40 * 1231647 * 2
def baseEnd_1231647 : Nat := 421617938445498606098843

theorem tailTrace_1231647 : CollatzResearch.WordTrace tailWord_1231647 prefixEnd_1231647 421617938445498606098843 := by
  unfold tailWord_1231647
  simp only [CollatzResearch.WordTrace]
  refine ⟨44921856568960742406005195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29947904379307161604003463 44921856568960742406005195)
  ·
    refine ⟨67382784853441113609007793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44921856568960742406005195 67382784853441113609007793)
    ·
      refine ⟨50537088640080835206755845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67382784853441113609007793 50537088640080835206755845)
      ·
        refine ⟨9475704120015156601266721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50537088640080835206755845 9475704120015156601266721)
        ·
          refine ⟨7106778090011367450950041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9475704120015156601266721 7106778090011367450950041)
          ·
            refine ⟨5330083567508525588212531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7106778090011367450950041 5330083567508525588212531)
            ·
              refine ⟨7995125351262788382318797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330083567508525588212531 7995125351262788382318797)
              ·
                refine ⟨2998172006723545643369549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7995125351262788382318797 2998172006723545643369549)
                ·
                  refine ⟨1124314502521329616263581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2998172006723545643369549 1124314502521329616263581)
                  ·
                    refine ⟨421617938445498606098843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124314502521329616263581 421617938445498606098843)
                    ·
                      rfl

theorem cell22_1231647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_1231647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231647 prefixEnd_1231647 := by exact prefixLift 1231647
  have htrace : WordTrace (prefixWord ++ tailWord_1231647) baseStart_1231647 baseEnd_1231647 := by
    simpa [prefixWord, tailWord_1231647, baseEnd_1231647] using wordTrace_append hprefix tailTrace_1231647
  have hstable : (prefixWord ++ tailWord_1231647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231647).length < 2 ^ (prefixWord ++ tailWord_1231647).sum := by decide
  have hdescent : baseEnd_1231647 < baseStart_1231647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231735 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 1, 6]
def baseStart_1231735 : Nat := 118140960795 + 1231735 * 2 ^ 59
def prefixEnd_1231735 : Nat := 4983230072969 + 3 ^ 40 * 1231735 * 2
def baseEnd_1231735 : Nat := 421648062643895709898573

theorem tailTrace_1231735 : CollatzResearch.WordTrace tailWord_1231735 prefixEnd_1231735 421648062643895709898573 := by
  unfold tailWord_1231735
  simp only [CollatzResearch.WordTrace]
  refine ⟨44925066192641933435208659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29950044128427955623472439 44925066192641933435208659)
  ·
    refine ⟨67387599288962900152812989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44925066192641933435208659 67387599288962900152812989)
    ·
      refine ⟨25270349733361087557304871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67387599288962900152812989 25270349733361087557304871)
      ·
        refine ⟨37905524600041631335957307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25270349733361087557304871 37905524600041631335957307)
        ·
          refine ⟨56858286900062447003935961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37905524600041631335957307 56858286900062447003935961)
          ·
            refine ⟨42643715175046835252951971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56858286900062447003935961 42643715175046835252951971)
            ·
              refine ⟨63965572762570252879427957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42643715175046835252951971 63965572762570252879427957)
              ·
                refine ⟨5996772446490961207446371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63965572762570252879427957 5996772446490961207446371)
                ·
                  refine ⟨8995158669736441811169557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5996772446490961207446371 8995158669736441811169557)
                  ·
                    refine ⟨421648062643895709898573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8995158669736441811169557 421648062643895709898573)
                    ·
                      rfl

theorem cell22_1231735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_1231735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231735 prefixEnd_1231735 := by exact prefixLift 1231735
  have htrace : WordTrace (prefixWord ++ tailWord_1231735) baseStart_1231735 baseEnd_1231735 := by
    simpa [prefixWord, tailWord_1231735, baseEnd_1231735] using wordTrace_append hprefix tailTrace_1231735
  have hstable : (prefixWord ++ tailWord_1231735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231735).length < 2 ^ (prefixWord ++ tailWord_1231735).sum := by decide
  have hdescent : baseEnd_1231735 < baseStart_1231735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231737 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_1231737 : Nat := 118140960795 + 1231737 * 2 ^ 59
def prefixEnd_1231737 : Nat := 4983230072969 + 3 ^ 40 * 1231737 * 2
def baseEnd_1231737 : Nat := 421648747284768371348567

theorem tailTrace_1231737 : CollatzResearch.WordTrace tailWord_1231737 prefixEnd_1231737 421648747284768371348567 := by
  unfold tailWord_1231737
  simp only [CollatzResearch.WordTrace]
  refine ⟨44925139138634687776781465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29950092759089791851187643 44925139138634687776781465)
  ·
    refine ⟨33693854353976015832586099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44925139138634687776781465 33693854353976015832586099)
    ·
      refine ⟨50540781530964023748879149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33693854353976015832586099 50540781530964023748879149)
      ·
        refine ⟨18952793074111508905829681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50540781530964023748879149 18952793074111508905829681)
        ·
          refine ⟨14214594805583631679372261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18952793074111508905829681 14214594805583631679372261)
          ·
            refine ⟨2665236526046930939882299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14214594805583631679372261 2665236526046930939882299)
            ·
              refine ⟨3997854789070396409823449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665236526046930939882299 3997854789070396409823449)
              ·
                refine ⟨2998391091802797307367587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3997854789070396409823449 2998391091802797307367587)
                ·
                  refine ⟨4497586637704195961051381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998391091802797307367587 4497586637704195961051381)
                  ·
                    refine ⟨421648747284768371348567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4497586637704195961051381 421648747284768371348567)
                    ·
                      rfl

theorem cell22_1231737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_1231737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231737 prefixEnd_1231737 := by exact prefixLift 1231737
  have htrace : WordTrace (prefixWord ++ tailWord_1231737) baseStart_1231737 baseEnd_1231737 := by
    simpa [prefixWord, tailWord_1231737, baseEnd_1231737] using wordTrace_append hprefix tailTrace_1231737
  have hstable : (prefixWord ++ tailWord_1231737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231737).length < 2 ^ (prefixWord ++ tailWord_1231737).sum := by decide
  have hdescent : baseEnd_1231737 < baseStart_1231737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231816 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 3, 3]
def baseStart_1231816 : Nat := 118140960795 + 1231816 * 2 ^ 59
def prefixEnd_1231816 : Nat := 4983230072969 + 3 ^ 40 * 1231816 * 2
def baseEnd_1231816 : Nat := 421675790599238498623325

theorem tailTrace_1231816 : CollatzResearch.WordTrace tailWord_1231816 prefixEnd_1231816 421675790599238498623325 := by
  unfold tailWord_1231816
  simp only [CollatzResearch.WordTrace]
  refine ⟨22464010252674242134453651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29952013670232322845938201 22464010252674242134453651)
  ·
    refine ⟨33696015379011363201680477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22464010252674242134453651 33696015379011363201680477)
    ·
      refine ⟨12636005767129261200630179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33696015379011363201680477 12636005767129261200630179)
      ·
        refine ⟨18954008650693891800945269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12636005767129261200630179 18954008650693891800945269)
        ·
          refine ⟨1776938311002552356338619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18954008650693891800945269 1776938311002552356338619)
          ·
            refine ⟨2665407466503828534507929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776938311002552356338619 2665407466503828534507929)
            ·
              refine ⟨1999055599877871400880947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2665407466503828534507929 1999055599877871400880947)
              ·
                refine ⟨2998583399816807101321421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999055599877871400880947 2998583399816807101321421)
                ·
                  refine ⟨1124468774931302662995533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2998583399816807101321421 1124468774931302662995533)
                  ·
                    refine ⟨421675790599238498623325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124468774931302662995533 421675790599238498623325)
                    ·
                      rfl

theorem cell22_1231816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_1231816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231816 prefixEnd_1231816 := by exact prefixLift 1231816
  have htrace : WordTrace (prefixWord ++ tailWord_1231816) baseStart_1231816 baseEnd_1231816 := by
    simpa [prefixWord, tailWord_1231816, baseEnd_1231816] using wordTrace_append hprefix tailTrace_1231816
  have hstable : (prefixWord ++ tailWord_1231816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231816).length < 2 ^ (prefixWord ++ tailWord_1231816).sum := by decide
  have hdescent : baseEnd_1231816 < baseStart_1231816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231964 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 7]
def baseStart_1231964 : Nat := 118140960795 + 1231964 * 2 ^ 59
def prefixEnd_1231964 : Nat := 4983230072969 + 3 ^ 40 * 1231964 * 2
def baseEnd_1231964 : Nat := 140575484674605148640957

theorem tailTrace_1231964 : CollatzResearch.WordTrace tailWord_1231964 prefixEnd_1231964 140575484674605148640957 := by
  unfold tailWord_1231964
  simp only [CollatzResearch.WordTrace]
  refine ⟨22466709254406152772647473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29955612339208203696863297 22466709254406152772647473)
  ·
    refine ⟨16850031940804614579485605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22466709254406152772647473 16850031940804614579485605)
    ·
      refine ⟨3159380988900865233653551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16850031940804614579485605 3159380988900865233653551)
      ·
        refine ⟨4739071483351297850480327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3159380988900865233653551 4739071483351297850480327)
        ·
          refine ⟨7108607225026946775720491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4739071483351297850480327 7108607225026946775720491)
          ·
            refine ⟨10662910837540420163580737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7108607225026946775720491 10662910837540420163580737)
            ·
              refine ⟨7997183128155315122685553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10662910837540420163580737 7997183128155315122685553)
              ·
                refine ⟨5997887346116486342014165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7997183128155315122685553 5997887346116486342014165)
                ·
                  refine ⟨140575484674605148640957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5997887346116486342014165 140575484674605148640957)
                  ·
                    rfl

theorem cell22_1231964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_1231964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231964 prefixEnd_1231964 := by exact prefixLift 1231964
  have htrace : WordTrace (prefixWord ++ tailWord_1231964) baseStart_1231964 baseEnd_1231964 := by
    simpa [prefixWord, tailWord_1231964, baseEnd_1231964] using wordTrace_append hprefix tailTrace_1231964
  have hstable : (prefixWord ++ tailWord_1231964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231964).length < 2 ^ (prefixWord ++ tailWord_1231964).sum := by decide
  have hdescent : baseEnd_1231964 < baseStart_1231964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231968 : List Nat := [2, 1, 1, 3, 2, 2, 4, 3, 1, 3]
def baseStart_1231968 : Nat := 118140960795 + 1231968 * 2 ^ 59
def prefixEnd_1231968 : Nat := 4983230072969 + 3 ^ 40 * 1231968 * 2
def baseEnd_1231968 : Nat := 421727823305560768822859

theorem tailTrace_1231968 : CollatzResearch.WordTrace tailWord_1231968 prefixEnd_1231968 421727823305560768822859 := by
  unfold tailWord_1231968
  simp only [CollatzResearch.WordTrace]
  refine ⟨22466782200398907114220279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29955709600531876152293705 22466782200398907114220279)
  ·
    refine ⟨33700173300598360671330419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22466782200398907114220279 33700173300598360671330419)
    ·
      refine ⟨50550259950897541006995629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33700173300598360671330419 50550259950897541006995629)
      ·
        refine ⟨18956347481586577877623361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50550259950897541006995629 18956347481586577877623361)
        ·
          refine ⟨14217260611189933408217521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18956347481586577877623361 14217260611189933408217521)
          ·
            refine ⟨10662945458392450056163141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14217260611189933408217521 10662945458392450056163141)
            ·
              refine ⟨1999302273448584385530589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10662945458392450056163141 1999302273448584385530589)
              ·
                refine ⟨749738352543219144573971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1999302273448584385530589 749738352543219144573971)
                ·
                  refine ⟨1124607528814828716860957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749738352543219144573971 1124607528814828716860957)
                  ·
                    refine ⟨421727823305560768822859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124607528814828716860957 421727823305560768822859)
                    ·
                      rfl

theorem cell22_1231968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 1, 3].length) (baseStart_1231968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231968 prefixEnd_1231968 := by exact prefixLift 1231968
  have htrace : WordTrace (prefixWord ++ tailWord_1231968) baseStart_1231968 baseEnd_1231968 := by
    simpa [prefixWord, tailWord_1231968, baseEnd_1231968] using wordTrace_append hprefix tailTrace_1231968
  have hstable : (prefixWord ++ tailWord_1231968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231968).length < 2 ^ (prefixWord ++ tailWord_1231968).sum := by decide
  have hdescent : baseEnd_1231968 < baseStart_1231968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1231981 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 5]
def baseStart_1231981 : Nat := 118140960795 + 1231981 * 2 ^ 59
def prefixEnd_1231981 : Nat := 4983230072969 + 3 ^ 40 * 1231981 * 2
def baseEnd_1231981 : Nat := 140577424490411022749273

theorem tailTrace_1231981 : CollatzResearch.WordTrace tailWord_1231981 prefixEnd_1231981 140577424490411022749273 := by
  unfold tailWord_1231981
  simp only [CollatzResearch.WordTrace]
  refine ⟨44934038549750717448663797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29956025699833811632442531 44934038549750717448663797)
  ·
    refine ⟨4212566114039129760812231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44934038549750717448663797 4212566114039129760812231)
    ·
      refine ⟨6318849171058694641218347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212566114039129760812231 6318849171058694641218347)
      ·
        refine ⟨9478273756588041961827521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6318849171058694641218347 9478273756588041961827521)
        ·
          refine ⟨7108705317441031471370641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9478273756588041961827521 7108705317441031471370641)
          ·
            refine ⟨5331528988080773603527981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7108705317441031471370641 5331528988080773603527981)
            ·
              refine ⟨1999323370530290101322993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5331528988080773603527981 1999323370530290101322993)
              ·
                refine ⟨1499492527897717575992245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999323370530290101322993 1499492527897717575992245)
                ·
                  refine ⟨140577424490411022749273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1499492527897717575992245 140577424490411022749273)
                  ·
                    rfl

theorem cell22_1231981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_1231981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1231981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1231981 prefixEnd_1231981 := by exact prefixLift 1231981
  have htrace : WordTrace (prefixWord ++ tailWord_1231981) baseStart_1231981 baseEnd_1231981 := by
    simpa [prefixWord, tailWord_1231981, baseEnd_1231981] using wordTrace_append hprefix tailTrace_1231981
  have hstable : (prefixWord ++ tailWord_1231981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1231981).length < 2 ^ (prefixWord ++ tailWord_1231981).sum := by decide
  have hdescent : baseEnd_1231981 < baseStart_1231981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1231981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232009 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 6]
def baseStart_1232009 : Nat := 118140960795 + 1232009 * 2 ^ 59
def prefixEnd_1232009 : Nat := 4983230072969 + 3 ^ 40 * 1232009 * 2
def baseEnd_1232009 : Nat := 140580619481150109515911

theorem tailTrace_1232009 : CollatzResearch.WordTrace tailWord_1232009 prefixEnd_1232009 140580619481150109515911 := by
  unfold tailWord_1232009
  simp only [CollatzResearch.WordTrace]
  refine ⟨44935059793649278230683081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29956706529099518820455387 44935059793649278230683081)
  ·
    refine ⟨33701294845236958673012311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44935059793649278230683081 33701294845236958673012311)
    ·
      refine ⟨50551942267855438009518467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33701294845236958673012311 50551942267855438009518467)
      ·
        refine ⟨75827913401783157014277701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50551942267855438009518467 75827913401783157014277701)
        ·
          refine ⟨14217733762834341940177069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75827913401783157014277701 14217733762834341940177069)
          ·
            refine ⟨5331650161062878227566401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14217733762834341940177069 5331650161062878227566401)
            ·
              refine ⟨3998737620797158670674801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5331650161062878227566401 3998737620797158670674801)
              ·
                refine ⟨2999053215597869003006101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3998737620797158670674801 2999053215597869003006101)
                ·
                  refine ⟨140580619481150109515911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2999053215597869003006101 140580619481150109515911)
                  ·
                    rfl

theorem cell22_1232009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_1232009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232009 prefixEnd_1232009 := by exact prefixLift 1232009
  have htrace : WordTrace (prefixWord ++ tailWord_1232009) baseStart_1232009 baseEnd_1232009 := by
    simpa [prefixWord, tailWord_1232009, baseEnd_1232009] using wordTrace_append hprefix tailTrace_1232009
  have hstable : (prefixWord ++ tailWord_1232009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232009).length < 2 ^ (prefixWord ++ tailWord_1232009).sum := by decide
  have hdescent : baseEnd_1232009 < baseStart_1232009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232180 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1232180 : Nat := 118140960795 + 1232180 * 2 ^ 59
def prefixEnd_1232180 : Nat := 4983230072969 + 3 ^ 40 * 1232180 * 2
def baseEnd_1232180 : Nat := 421800395238062882522209

theorem tailTrace_1232180 : CollatzResearch.WordTrace tailWord_1232180 prefixEnd_1232180 421800395238062882522209 := by
  unfold tailWord_1232180
  simp only [CollatzResearch.WordTrace]
  refine ⟨22470648338014887217578997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29960864450686516290105329 22470648338014887217578997)
  ·
    refine ⟨2106623281688895676648031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22470648338014887217578997 2106623281688895676648031)
    ·
      refine ⟨3159934922533343514972047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2106623281688895676648031 3159934922533343514972047)
      ·
        refine ⟨4739902383800015272458071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3159934922533343514972047 4739902383800015272458071)
        ·
          refine ⟨7109853575700022908687107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4739902383800015272458071 7109853575700022908687107)
          ·
            refine ⟨10664780363550034363030661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7109853575700022908687107 10664780363550034363030661)
            ·
              refine ⟨1999646318165631443068249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10664780363550034363030661 1999646318165631443068249)
              ·
                refine ⟨1499734738624223582301187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999646318165631443068249 1499734738624223582301187)
                ·
                  refine ⟨2249602107936335373451781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499734738624223582301187 2249602107936335373451781)
                  ·
                    refine ⟨421800395238062882522209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2249602107936335373451781 421800395238062882522209)
                    ·
                      rfl

theorem cell22_1232180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1232180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232180 prefixEnd_1232180 := by exact prefixLift 1232180
  have htrace : WordTrace (prefixWord ++ tailWord_1232180) baseStart_1232180 baseEnd_1232180 := by
    simpa [prefixWord, tailWord_1232180, baseEnd_1232180] using wordTrace_append hprefix tailTrace_1232180
  have hstable : (prefixWord ++ tailWord_1232180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232180).length < 2 ^ (prefixWord ++ tailWord_1232180).sum := by decide
  have hdescent : baseEnd_1232180 < baseStart_1232180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232191 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 1, 6]
def baseStart_1232191 : Nat := 118140960795 + 1232191 * 2 ^ 59
def prefixEnd_1232191 : Nat := 4983230072969 + 3 ^ 40 * 1232191 * 2
def baseEnd_1232191 : Nat := 421804160762862520497175

theorem tailTrace_1232191 : CollatzResearch.WordTrace tailWord_1232191 prefixEnd_1232191 421804160762862520497175 := by
  unfold tailWord_1232191
  simp only [CollatzResearch.WordTrace]
  refine ⟨44941697878989923313808427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29961131919326615542538951 44941697878989923313808427)
  ·
    refine ⟨67412546818484884970712641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44941697878989923313808427 67412546818484884970712641)
    ·
      refine ⟨50559410113863663728034481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67412546818484884970712641 50559410113863663728034481)
      ·
        refine ⟨37919557585397747796025861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50559410113863663728034481 37919557585397747796025861)
        ·
          refine ⟨7109917047262077711754849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37919557585397747796025861 7109917047262077711754849)
          ·
            refine ⟨5332437785446558283816137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7109917047262077711754849 5332437785446558283816137)
            ·
              refine ⟨3999328339084918712862103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5332437785446558283816137 3999328339084918712862103)
              ·
                refine ⟨5998992508627378069293155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999328339084918712862103 5998992508627378069293155)
                ·
                  refine ⟨8998488762941067103939733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5998992508627378069293155 8998488762941067103939733)
                  ·
                    refine ⟨421804160762862520497175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8998488762941067103939733 421804160762862520497175)
                    ·
                      rfl

theorem cell22_1232191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_1232191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232191 prefixEnd_1232191 := by exact prefixLift 1232191
  have htrace : WordTrace (prefixWord ++ tailWord_1232191) baseStart_1232191 baseEnd_1232191 := by
    simpa [prefixWord, tailWord_1232191, baseEnd_1232191] using wordTrace_append hprefix tailTrace_1232191
  have hstable : (prefixWord ++ tailWord_1232191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232191).length < 2 ^ (prefixWord ++ tailWord_1232191).sum := by decide
  have hdescent : baseEnd_1232191 < baseStart_1232191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232227 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 2, 3]
def baseStart_1232227 : Nat := 118140960795 + 1232227 * 2 ^ 59
def prefixEnd_1232227 : Nat := 4983230072969 + 3 ^ 40 * 1232227 * 2
def baseEnd_1232227 : Nat := 421816484298570426597065

theorem tailTrace_1232227 : CollatzResearch.WordTrace tailWord_1232227 prefixEnd_1232227 421816484298570426597065 := by
  unfold tailWord_1232227
  simp only [CollatzResearch.WordTrace]
  refine ⟨44943010906859501462118935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29962007271239667641412623 44943010906859501462118935)
  ·
    refine ⟨67414516360289252193178403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44943010906859501462118935 67414516360289252193178403)
    ·
      refine ⟨101121774540433878289767605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67414516360289252193178403 101121774540433878289767605)
      ·
        refine ⟨9480166363165676089665713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101121774540433878289767605 9480166363165676089665713)
        ·
          refine ⟨7110124772374257067249285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9480166363165676089665713 7110124772374257067249285)
          ·
            refine ⟨1333148394820173200109241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7110124772374257067249285 1333148394820173200109241)
            ·
              refine ⟨999861296115129900081931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1333148394820173200109241 999861296115129900081931)
              ·
                refine ⟨1499791944172694850122897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999861296115129900081931 1499791944172694850122897)
                ·
                  refine ⟨1124843958129521137592173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1499791944172694850122897 1124843958129521137592173)
                  ·
                    refine ⟨421816484298570426597065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124843958129521137592173 421816484298570426597065)
                    ·
                      rfl

theorem cell22_1232227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 3].length) (baseStart_1232227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232227 prefixEnd_1232227 := by exact prefixLift 1232227
  have htrace : WordTrace (prefixWord ++ tailWord_1232227) baseStart_1232227 baseEnd_1232227 := by
    simpa [prefixWord, tailWord_1232227, baseEnd_1232227] using wordTrace_append hprefix tailTrace_1232227
  have hstable : (prefixWord ++ tailWord_1232227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232227).length < 2 ^ (prefixWord ++ tailWord_1232227).sum := by decide
  have hdescent : baseEnd_1232227 < baseStart_1232227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232268 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 5]
def baseStart_1232268 : Nat := 118140960795 + 1232268 * 2 ^ 59
def prefixEnd_1232268 : Nat := 4983230072969 + 3 ^ 40 * 1232268 * 2
def baseEnd_1232268 : Nat := 140610173145486662107313

theorem tailTrace_1232268 : CollatzResearch.WordTrace tailWord_1232268 prefixEnd_1232268 140610173145486662107313 := by
  unfold tailWord_1232268
  simp only [CollatzResearch.WordTrace]
  refine ⟨22472253149855482732180729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29963004199807310309574305 22472253149855482732180729)
  ·
    refine ⟨16854189862391612049135547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22472253149855482732180729 16854189862391612049135547)
    ·
      refine ⟨25281284793587418073703321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16854189862391612049135547 25281284793587418073703321)
      ·
        refine ⟨18960963595190563555277491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25281284793587418073703321 18960963595190563555277491)
        ·
          refine ⟨28441445392785845332916237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18960963595190563555277491 28441445392785845332916237)
          ·
            refine ⟨10665542022294691999843589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28441445392785845332916237 10665542022294691999843589)
            ·
              refine ⟨1999789129180254749970673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10665542022294691999843589 1999789129180254749970673)
              ·
                refine ⟨1499841846885191062478005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999789129180254749970673 1499841846885191062478005)
                ·
                  refine ⟨140610173145486662107313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1499841846885191062478005 140610173145486662107313)
                  ·
                    rfl

theorem cell22_1232268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_1232268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232268 prefixEnd_1232268 := by exact prefixLift 1232268
  have htrace : WordTrace (prefixWord ++ tailWord_1232268) baseStart_1232268 baseEnd_1232268 := by
    simpa [prefixWord, tailWord_1232268, baseEnd_1232268] using wordTrace_append hprefix tailTrace_1232268
  have hstable : (prefixWord ++ tailWord_1232268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232268).length < 2 ^ (prefixWord ++ tailWord_1232268).sum := by decide
  have hdescent : baseEnd_1232268 < baseStart_1232268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232330 : List Nat := [3, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_1232330 : Nat := 118140960795 + 1232330 * 2 ^ 59
def prefixEnd_1232330 : Nat := 4983230072969 + 3 ^ 40 * 1232330 * 2
def baseEnd_1232330 : Nat := 140617247767837497090583

theorem tailTrace_1232330 : CollatzResearch.WordTrace tailWord_1232330 prefixEnd_1232330 140617247767837497090583 := by
  unfold tailWord_1232330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11236691906371587513279611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29964511750324233368745629 11236691906371587513279611)
  ·
    refine ⟨16855037859557381269919417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11236691906371587513279611 16855037859557381269919417)
    ·
      refine ⟨12641278394668035952439563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16855037859557381269919417 12641278394668035952439563)
      ·
        refine ⟨18961917592002053928659345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12641278394668035952439563 18961917592002053928659345)
        ·
          refine ⟨14221438194001540446494509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18961917592002053928659345 14221438194001540446494509)
          ·
            refine ⟨5333039322750577667435441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14221438194001540446494509 5333039322750577667435441)
            ·
              refine ⟨3999779492062933250576581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5333039322750577667435441 3999779492062933250576581)
              ·
                refine ⟨749958654761799984483109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3999779492062933250576581 749958654761799984483109)
                ·
                  refine ⟨140617247767837497090583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749958654761799984483109 140617247767837497090583)
                  ·
                    rfl

theorem cell22_1232330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_1232330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232330 prefixEnd_1232330 := by exact prefixLift 1232330
  have htrace : WordTrace (prefixWord ++ tailWord_1232330) baseStart_1232330 baseEnd_1232330 := by
    simpa [prefixWord, tailWord_1232330, baseEnd_1232330] using wordTrace_append hprefix tailTrace_1232330
  have hstable : (prefixWord ++ tailWord_1232330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232330).length < 2 ^ (prefixWord ++ tailWord_1232330).sum := by decide
  have hdescent : baseEnd_1232330 < baseStart_1232330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232345 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 1, 5]
def baseStart_1232345 : Nat := 118140960795 + 1232345 * 2 ^ 59
def prefixEnd_1232345 : Nat := 4983230072969 + 3 ^ 40 * 1232345 * 2
def baseEnd_1232345 : Nat := 421856878110057452146703

theorem tailTrace_1232345 : CollatzResearch.WordTrace tailWord_1232345 prefixEnd_1232345 421856878110057452146703 := by
  unfold tailWord_1232345
  simp only [CollatzResearch.WordTrace]
  refine ⟨44947314720432007614914489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29964876480288005076609659 44947314720432007614914489)
  ·
    refine ⟨33710486040324005711185867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44947314720432007614914489 33710486040324005711185867)
    ·
      refine ⟨50565729060486008566778801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33710486040324005711185867 50565729060486008566778801)
      ·
        refine ⟨37924296795364506425084101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50565729060486008566778801 37924296795364506425084101)
        ·
          refine ⟨7110805649130844954703269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37924296795364506425084101 7110805649130844954703269)
          ·
            refine ⟨1333276059212033429006863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7110805649130844954703269 1333276059212033429006863)
            ·
              refine ⟨1999914088818050143510295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333276059212033429006863 1999914088818050143510295)
              ·
                refine ⟨2999871133227075215265443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999914088818050143510295 2999871133227075215265443)
                ·
                  refine ⟨4499806699840612822898165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2999871133227075215265443 4499806699840612822898165)
                  ·
                    refine ⟨421856878110057452146703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4499806699840612822898165 421856878110057452146703)
                    ·
                      rfl

theorem cell22_1232345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_1232345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232345 prefixEnd_1232345 := by exact prefixLift 1232345
  have htrace : WordTrace (prefixWord ++ tailWord_1232345) baseStart_1232345 baseEnd_1232345 := by
    simpa [prefixWord, tailWord_1232345, baseEnd_1232345] using wordTrace_append hprefix tailTrace_1232345
  have hstable : (prefixWord ++ tailWord_1232345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232345).length < 2 ^ (prefixWord ++ tailWord_1232345).sum := by decide
  have hdescent : baseEnd_1232345 < baseStart_1232345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232396 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 2, 3]
def baseStart_1232396 : Nat := 118140960795 + 1232396 * 2 ^ 59
def prefixEnd_1232396 : Nat := 4983230072969 + 3 ^ 40 * 1232396 * 2
def baseEnd_1232396 : Nat := 421874336452310319121547

theorem tailTrace_1232396 : CollatzResearch.WordTrace tailWord_1232396 prefixEnd_1232396 421874336452310319121547 := by
  unfold tailWord_1232396
  simp only [CollatzResearch.WordTrace]
  refine ⟨22474587421623621662510521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29966116562164828883347361 22474587421623621662510521)
  ·
    refine ⟨16855940566217716246882891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22474587421623621662510521 16855940566217716246882891)
    ·
      refine ⟨25283910849326574370324337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16855940566217716246882891 25283910849326574370324337)
      ·
        refine ⟨18962933136994930777743253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25283910849326574370324337 18962933136994930777743253)
        ·
          refine ⟨888887490796637380206715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18962933136994930777743253 888887490796637380206715)
          ·
            refine ⟨1333331236194956070310073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888887490796637380206715 1333331236194956070310073)
            ·
              refine ⟨999998427146217052732555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1333331236194956070310073 999998427146217052732555)
              ·
                refine ⟨1499997640719325579098833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999998427146217052732555 1499997640719325579098833)
                ·
                  refine ⟨1124998230539494184324125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1499997640719325579098833 1124998230539494184324125)
                  ·
                    refine ⟨421874336452310319121547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124998230539494184324125 421874336452310319121547)
                    ·
                      rfl

theorem cell22_1232396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_1232396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232396 prefixEnd_1232396 := by exact prefixLift 1232396
  have htrace : WordTrace (prefixWord ++ tailWord_1232396) baseStart_1232396 baseEnd_1232396 := by
    simpa [prefixWord, tailWord_1232396, baseEnd_1232396] using wordTrace_append hprefix tailTrace_1232396
  have hstable : (prefixWord ++ tailWord_1232396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232396).length < 2 ^ (prefixWord ++ tailWord_1232396).sum := by decide
  have hdescent : baseEnd_1232396 < baseStart_1232396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232441 : List Nat := [1, 2, 1, 5, 1, 4, 2, 2, 1, 3]
def baseStart_1232441 : Nat := 118140960795 + 1232441 * 2 ^ 59
def prefixEnd_1232441 : Nat := 4983230072969 + 3 ^ 40 * 1232441 * 2
def baseEnd_1232441 : Nat := 421889740871945201746409

theorem tailTrace_1232441 : CollatzResearch.WordTrace tailWord_1232441 prefixEnd_1232441 421889740871945201746409 := by
  unfold tailWord_1232441
  simp only [CollatzResearch.WordTrace]
  refine ⟨44950816128084216010409177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29967210752056144006939451 44950816128084216010409177)
  ·
    refine ⟨33713112096063162007806883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44950816128084216010409177 33713112096063162007806883)
    ·
      refine ⟨50569668144094743011710325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33713112096063162007806883 50569668144094743011710325)
      ·
        refine ⟨4740906388508882157347843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50569668144094743011710325 4740906388508882157347843)
        ·
          refine ⟨7111359582763323236021765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740906388508882157347843 7111359582763323236021765)
          ·
            refine ⟨1333379921768123106754081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7111359582763323236021765 1333379921768123106754081)
            ·
              refine ⟨1000034941326092330065561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1333379921768123106754081 1000034941326092330065561)
              ·
                refine ⟨750026205994569247549171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000034941326092330065561 750026205994569247549171)
                ·
                  refine ⟨1125039308991853871323757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750026205994569247549171 1125039308991853871323757)
                  ·
                    refine ⟨421889740871945201746409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125039308991853871323757 421889740871945201746409)
                    ·
                      rfl

theorem cell22_1232441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 3].length) (baseStart_1232441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232441 prefixEnd_1232441 := by exact prefixLift 1232441
  have htrace : WordTrace (prefixWord ++ tailWord_1232441) baseStart_1232441 baseEnd_1232441 := by
    simpa [prefixWord, tailWord_1232441, baseEnd_1232441] using wordTrace_append hprefix tailTrace_1232441
  have hstable : (prefixWord ++ tailWord_1232441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232441).length < 2 ^ (prefixWord ++ tailWord_1232441).sum := by decide
  have hdescent : baseEnd_1232441 < baseStart_1232441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232448 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 6]
def baseStart_1232448 : Nat := 118140960795 + 1232448 * 2 ^ 59
def prefixEnd_1232448 : Nat := 4983230072969 + 3 ^ 40 * 1232448 * 2
def baseEnd_1232448 : Nat := 140630712371666505607129

theorem tailTrace_1232448 : CollatzResearch.WordTrace tailWord_1232448 prefixEnd_1232448 140630712371666505607129 := by
  unfold tailWord_1232448
  simp only [CollatzResearch.WordTrace]
  refine ⟨22475535719529428102956999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29967380959372570803942665 22475535719529428102956999)
  ·
    refine ⟨33713303579294142154435499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22475535719529428102956999 33713303579294142154435499)
    ·
      refine ⟨50569955368941213231653249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33713303579294142154435499 50569955368941213231653249)
      ·
        refine ⟨37927466526705909923739937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50569955368941213231653249 37927466526705909923739937)
        ·
          refine ⟨28445599895029432442804953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37927466526705909923739937 28445599895029432442804953)
          ·
            refine ⟨21334199921272074332103715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28445599895029432442804953 21334199921272074332103715)
            ·
              refine ⟨32001299881908111498155573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21334199921272074332103715 32001299881908111498155573)
              ·
                refine ⟨3000121863928885452952085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32001299881908111498155573 3000121863928885452952085)
                ·
                  refine ⟨140630712371666505607129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3000121863928885452952085 140630712371666505607129)
                  ·
                    rfl

theorem cell22_1232448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_1232448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232448 prefixEnd_1232448 := by exact prefixLift 1232448
  have htrace : WordTrace (prefixWord ++ tailWord_1232448) baseStart_1232448 baseEnd_1232448 := by
    simpa [prefixWord, tailWord_1232448, baseEnd_1232448] using wordTrace_append hprefix tailTrace_1232448
  have hstable : (prefixWord ++ tailWord_1232448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232448).length < 2 ^ (prefixWord ++ tailWord_1232448).sum := by decide
  have hdescent : baseEnd_1232448 < baseStart_1232448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232480 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 4, 3]
def baseStart_1232480 : Nat := 118140960795 + 1232480 * 2 ^ 59
def prefixEnd_1232480 : Nat := 4983230072969 + 3 ^ 40 * 1232480 * 2
def baseEnd_1232480 : Nat := 421903091368962100021289

theorem tailTrace_1232480 : CollatzResearch.WordTrace tailWord_1232480 prefixEnd_1232480 421903091368962100021289 := by
  unfold tailWord_1232480
  simp only [CollatzResearch.WordTrace]
  refine ⟨22476119287471462835539447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29968159049961950447385929 22476119287471462835539447)
  ·
    refine ⟨33714178931207194253309171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22476119287471462835539447 33714178931207194253309171)
    ·
      refine ⟨50571268396810791379963757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33714178931207194253309171 50571268396810791379963757)
      ·
        refine ⟨18964225648804046767486409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50571268396810791379963757 18964225648804046767486409)
        ·
          refine ⟨14223169236603035075614807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18964225648804046767486409 14223169236603035075614807)
          ·
            refine ⟨21334753854904552613422211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14223169236603035075614807 21334753854904552613422211)
            ·
              refine ⟨32002130782356828920133317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21334753854904552613422211 32002130782356828920133317)
              ·
                refine ⟨6000399521691905422524997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32002130782356828920133317 6000399521691905422524997)
                ·
                  refine ⟨1125074910317232266723437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6000399521691905422524997 1125074910317232266723437)
                  ·
                    refine ⟨421903091368962100021289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125074910317232266723437 421903091368962100021289)
                    ·
                      rfl

theorem cell22_1232480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 3].length) (baseStart_1232480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232480 prefixEnd_1232480 := by exact prefixLift 1232480
  have htrace : WordTrace (prefixWord ++ tailWord_1232480) baseStart_1232480 baseEnd_1232480 := by
    simpa [prefixWord, tailWord_1232480, baseEnd_1232480] using wordTrace_append hprefix tailTrace_1232480
  have hstable : (prefixWord ++ tailWord_1232480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232480).length < 2 ^ (prefixWord ++ tailWord_1232480).sum := by decide
  have hdescent : baseEnd_1232480 < baseStart_1232480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232484 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_1232484 : Nat := 118140960795 + 1232484 * 2 ^ 59
def prefixEnd_1232484 : Nat := 4983230072969 + 3 ^ 40 * 1232484 * 2
def baseEnd_1232484 : Nat := 421904460650707422921277

theorem tailTrace_1232484 : CollatzResearch.WordTrace tailWord_1232484 prefixEnd_1232484 421904460650707422921277 := by
  unfold tailWord_1232484
  simp only [CollatzResearch.WordTrace]
  refine ⟨22476192233464217177112253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29968256311285622902816337 22476192233464217177112253)
  ·
    refine ⟨8428572087549081441417095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22476192233464217177112253 8428572087549081441417095)
    ·
      refine ⟨12642858131323622162125643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8428572087549081441417095 12642858131323622162125643)
      ·
        refine ⟨18964287196985433243188465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12642858131323622162125643 18964287196985433243188465)
        ·
          refine ⟨14223215397739074932391349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18964287196985433243188465 14223215397739074932391349)
          ·
            refine ⟨1333426443538038274911689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14223215397739074932391349 1333426443538038274911689)
            ·
              refine ⟨1000069832653528706183767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1333426443538038274911689 1000069832653528706183767)
              ·
                refine ⟨1500104748980293059275651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000069832653528706183767 1500104748980293059275651)
                ·
                  refine ⟨2250157123470439588913477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500104748980293059275651 2250157123470439588913477)
                  ·
                    refine ⟨421904460650707422921277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2250157123470439588913477 421904460650707422921277)
                    ·
                      rfl

theorem cell22_1232484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_1232484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232484 prefixEnd_1232484 := by exact prefixLift 1232484
  have htrace : WordTrace (prefixWord ++ tailWord_1232484) baseStart_1232484 baseEnd_1232484 := by
    simpa [prefixWord, tailWord_1232484, baseEnd_1232484] using wordTrace_append hprefix tailTrace_1232484
  have hstable : (prefixWord ++ tailWord_1232484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232484).length < 2 ^ (prefixWord ++ tailWord_1232484).sum := by decide
  have hdescent : baseEnd_1232484 < baseStart_1232484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232572 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 5]
def baseStart_1232572 : Nat := 118140960795 + 1232572 * 2 ^ 59
def prefixEnd_1232572 : Nat := 4983230072969 + 3 ^ 40 * 1232572 * 2
def baseEnd_1232572 : Nat := 140644861616368175573669

theorem tailTrace_1232572 : CollatzResearch.WordTrace tailWord_1232572 prefixEnd_1232572 140644861616368175573669 := by
  unfold tailWord_1232572
  simp only [CollatzResearch.WordTrace]
  refine ⟨22477797045304812691713985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29970396060406416922285313 22477797045304812691713985)
  ·
    refine ⟨16858347783978609518785489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22477797045304812691713985 16858347783978609518785489)
    ·
      refine ⟨12643760837983957139089117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16858347783978609518785489 12643760837983957139089117)
      ·
        refine ⟨4741410314243983927158419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12643760837983957139089117 4741410314243983927158419)
        ·
          refine ⟨7112115471365975890737629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4741410314243983927158419 7112115471365975890737629)
          ·
            refine ⟨2667043301762240959026611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7112115471365975890737629 2667043301762240959026611)
            ·
              refine ⟨4000564952643361438539917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2667043301762240959026611 4000564952643361438539917)
              ·
                refine ⟨1500211857241260539452469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4000564952643361438539917 1500211857241260539452469)
                ·
                  refine ⟨140644861616368175573669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1500211857241260539452469 140644861616368175573669)
                  ·
                    rfl

theorem cell22_1232572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_1232572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232572 prefixEnd_1232572 := by exact prefixLift 1232572
  have htrace : WordTrace (prefixWord ++ tailWord_1232572) baseStart_1232572 baseEnd_1232572 := by
    simpa [prefixWord, tailWord_1232572, baseEnd_1232572] using wordTrace_append hprefix tailTrace_1232572
  have hstable : (prefixWord ++ tailWord_1232572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232572).length < 2 ^ (prefixWord ++ tailWord_1232572).sum := by decide
  have hdescent : baseEnd_1232572 < baseStart_1232572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232666 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_1232666 : Nat := 118140960795 + 1232666 * 2 ^ 59
def prefixEnd_1232666 : Nat := 4983230072969 + 3 ^ 40 * 1232666 * 2
def baseEnd_1232666 : Nat := 421966762970119614870719

theorem tailTrace_1232666 : CollatzResearch.WordTrace tailWord_1232666 prefixEnd_1232666 421966762970119614870719 := by
  unfold tailWord_1232666
  simp only [CollatzResearch.WordTrace]
  refine ⟨11239755638067269859337463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29972681701512719624899901 11239755638067269859337463)
  ·
    refine ⟨16859633457100904789006195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11239755638067269859337463 16859633457100904789006195)
    ·
      refine ⟨25289450185651357183509293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16859633457100904789006195 25289450185651357183509293)
      ·
        refine ⟨9483543819619258943815985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25289450185651357183509293 9483543819619258943815985)
        ·
          refine ⟨7112657864714444207861989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9483543819619258943815985 7112657864714444207861989)
          ·
            refine ⟨1333623349633958288974123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7112657864714444207861989 1333623349633958288974123)
            ·
              refine ⟨2000435024450937433461185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333623349633958288974123 2000435024450937433461185)
              ·
                refine ⟨1500326268338203075095889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2000435024450937433461185 1500326268338203075095889)
                ·
                  refine ⟨1125244701253652306321917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1500326268338203075095889 1125244701253652306321917)
                  ·
                    refine ⟨421966762970119614870719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125244701253652306321917 421966762970119614870719)
                    ·
                      rfl

theorem cell22_1232666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_1232666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232666 prefixEnd_1232666 := by exact prefixLift 1232666
  have htrace : WordTrace (prefixWord ++ tailWord_1232666) baseStart_1232666 baseEnd_1232666 := by
    simpa [prefixWord, tailWord_1232666, baseEnd_1232666] using wordTrace_append hprefix tailTrace_1232666
  have hstable : (prefixWord ++ tailWord_1232666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232666).length < 2 ^ (prefixWord ++ tailWord_1232666).sum := by decide
  have hdescent : baseEnd_1232666 < baseStart_1232666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232675 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 1, 8]
def baseStart_1232675 : Nat := 118140960795 + 1232675 * 2 ^ 59
def prefixEnd_1232675 : Nat := 4983230072969 + 3 ^ 40 * 1232675 * 2
def baseEnd_1232675 : Nat := 421969843854046591395691

theorem tailTrace_1232675 : CollatzResearch.WordTrace tailWord_1232675 prefixEnd_1232675 421969843854046591395691 := by
  unfold tailWord_1232675
  simp only [CollatzResearch.WordTrace]
  refine ⟨44959350809236473974427479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29972900539490982649618319 44959350809236473974427479)
  ·
    refine ⟨67439026213854710961641219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44959350809236473974427479 67439026213854710961641219)
    ·
      refine ⟨101158539320782066442461829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67439026213854710961641219 101158539320782066442461829)
      ·
        refine ⟨18967226122646637457961593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101158539320782066442461829 18967226122646637457961593)
        ·
          refine ⟨14225419591984978093471195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18967226122646637457961593 14225419591984978093471195)
          ·
            refine ⟨21338129387977467140206793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14225419591984978093471195 21338129387977467140206793)
            ·
              refine ⟨16003597040983100355155095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21338129387977467140206793 16003597040983100355155095)
              ·
                refine ⟨24005395561474650532732643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16003597040983100355155095 24005395561474650532732643)
                ·
                  refine ⟨36008093342211975799098965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24005395561474650532732643 36008093342211975799098965)
                  ·
                    refine ⟨421969843854046591395691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36008093342211975799098965 421969843854046591395691)
                    ·
                      rfl

theorem cell22_1232675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_1232675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232675 prefixEnd_1232675 := by exact prefixLift 1232675
  have htrace : WordTrace (prefixWord ++ tailWord_1232675) baseStart_1232675 baseEnd_1232675 := by
    simpa [prefixWord, tailWord_1232675, baseEnd_1232675] using wordTrace_append hprefix tailTrace_1232675
  have hstable : (prefixWord ++ tailWord_1232675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232675).length < 2 ^ (prefixWord ++ tailWord_1232675).sum := by decide
  have hdescent : baseEnd_1232675 < baseStart_1232675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232711 : List Nat := [1, 1, 4, 1, 2, 1, 5, 3, 1, 3]
def baseStart_1232711 : Nat := 118140960795 + 1232711 * 2 ^ 59
def prefixEnd_1232711 : Nat := 4983230072969 + 3 ^ 40 * 1232711 * 2
def baseEnd_1232711 : Nat := 421982167389754497495581

theorem tailTrace_1232711 : CollatzResearch.WordTrace tailWord_1232711 prefixEnd_1232711 421982167389754497495581 := by
  unfold tailWord_1232711
  simp only [CollatzResearch.WordTrace]
  refine ⟨44960663837106052122737987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29973775891404034748491991 44960663837106052122737987)
  ·
    refine ⟨67440995755659078184106981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44960663837106052122737987 67440995755659078184106981)
    ·
      refine ⟨12645186704186077159520059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67440995755659078184106981 12645186704186077159520059)
      ·
        refine ⟨18967780056279115739280089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12645186704186077159520059 18967780056279115739280089)
        ·
          refine ⟨14225835042209336804460067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18967780056279115739280089 14225835042209336804460067)
          ·
            refine ⟨21338752563314005206690101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14225835042209336804460067 21338752563314005206690101)
            ·
              refine ⟨2000508052810687988127197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21338752563314005206690101 2000508052810687988127197)
              ·
                refine ⟨750190519804007995547699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2000508052810687988127197 750190519804007995547699)
                ·
                  refine ⟨1125285779706011993321549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750190519804007995547699 1125285779706011993321549)
                  ·
                    refine ⟨421982167389754497495581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125285779706011993321549 421982167389754497495581)
                    ·
                      rfl

theorem cell22_1232711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_1232711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232711 prefixEnd_1232711 := by exact prefixLift 1232711
  have htrace : WordTrace (prefixWord ++ tailWord_1232711) baseStart_1232711 baseEnd_1232711 := by
    simpa [prefixWord, tailWord_1232711, baseEnd_1232711] using wordTrace_append hprefix tailTrace_1232711
  have hstable : (prefixWord ++ tailWord_1232711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232711).length < 2 ^ (prefixWord ++ tailWord_1232711).sum := by decide
  have hdescent : baseEnd_1232711 < baseStart_1232711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232737 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1232737 : Nat := 118140960795 + 1232737 * 2 ^ 59
def prefixEnd_1232737 : Nat := 4983230072969 + 3 ^ 40 * 1232737 * 2
def baseEnd_1232737 : Nat := 421991067721099096345501

theorem tailTrace_1232737 : CollatzResearch.WordTrace tailWord_1232737 prefixEnd_1232737 421991067721099096345501 := by
  unfold tailWord_1232737
  simp only [CollatzResearch.WordTrace]
  refine ⟨44961612135011858563184465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29974408090007905708789643 44961612135011858563184465)
  ·
    refine ⟨33721209101258893922388349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44961612135011858563184465 33721209101258893922388349)
    ·
      refine ⟨12645453412972085220895631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33721209101258893922388349 12645453412972085220895631)
      ·
        refine ⟨18968180119458127831343447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12645453412972085220895631 18968180119458127831343447)
        ·
          refine ⟨28452270179187191747015171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18968180119458127831343447 28452270179187191747015171)
          ·
            refine ⟨42678405268780787620522757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28452270179187191747015171 42678405268780787620522757)
            ·
              refine ⟨8002200987896397678848017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42678405268780787620522757 8002200987896397678848017)
              ·
                refine ⟨6001650740922298259136013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8002200987896397678848017 6001650740922298259136013)
                ·
                  refine ⟨2250619027845861847176005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6001650740922298259136013 2250619027845861847176005)
                  ·
                    refine ⟨421991067721099096345501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2250619027845861847176005 421991067721099096345501)
                    ·
                      rfl

theorem cell22_1232737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1232737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232737 prefixEnd_1232737 := by exact prefixLift 1232737
  have htrace : WordTrace (prefixWord ++ tailWord_1232737) baseStart_1232737 baseEnd_1232737 := by
    simpa [prefixWord, tailWord_1232737, baseEnd_1232737] using wordTrace_append hprefix tailTrace_1232737
  have hstable : (prefixWord ++ tailWord_1232737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232737).length < 2 ^ (prefixWord ++ tailWord_1232737).sum := by decide
  have hdescent : baseEnd_1232737 < baseStart_1232737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232771 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 1, 4]
def baseStart_1232771 : Nat := 118140960795 + 1232771 * 2 ^ 59
def prefixEnd_1232771 : Nat := 4983230072969 + 3 ^ 40 * 1232771 * 2
def baseEnd_1232771 : Nat := 422002706615934340995397

theorem tailTrace_1232771 : CollatzResearch.WordTrace tailWord_1232771 prefixEnd_1232771 422002706615934340995397 := by
  unfold tailWord_1232771
  simp only [CollatzResearch.WordTrace]
  refine ⟨44962852216888682369922167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29975234811259121579948111 44962852216888682369922167)
  ·
    refine ⟨67444278325333023554883251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44962852216888682369922167 67444278325333023554883251)
    ·
      refine ⟨101166417487999535332324877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67444278325333023554883251 101166417487999535332324877)
      ·
        refine ⟨37937406557999825749621829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101166417487999535332324877 37937406557999825749621829)
        ·
          refine ⟨7113263729624967328054093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37937406557999825749621829 7113263729624967328054093)
          ·
            refine ⟨2667473898609362748020285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7113263729624967328054093 2667473898609362748020285)
            ·
              refine ⟨1000302711978511030507607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2667473898609362748020285 1000302711978511030507607)
              ·
                refine ⟨1500454067967766545761411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000302711978511030507607 1500454067967766545761411)
                ·
                  refine ⟨2250681101951649818642117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500454067967766545761411 2250681101951649818642117)
                  ·
                    refine ⟨422002706615934340995397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2250681101951649818642117 422002706615934340995397)
                    ·
                      rfl

theorem cell22_1232771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 4].length) (baseStart_1232771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232771 prefixEnd_1232771 := by exact prefixLift 1232771
  have htrace : WordTrace (prefixWord ++ tailWord_1232771) baseStart_1232771 baseEnd_1232771 := by
    simpa [prefixWord, tailWord_1232771, baseEnd_1232771] using wordTrace_append hprefix tailTrace_1232771
  have hstable : (prefixWord ++ tailWord_1232771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232771).length < 2 ^ (prefixWord ++ tailWord_1232771).sum := by decide
  have hdescent : baseEnd_1232771 < baseStart_1232771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232784 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 2, 3]
def baseStart_1232784 : Nat := 118140960795 + 1232784 * 2 ^ 59
def prefixEnd_1232784 : Nat := 4983230072969 + 3 ^ 40 * 1232784 * 2
def baseEnd_1232784 : Nat := 422007156781606640420357

theorem tailTrace_1232784 : CollatzResearch.WordTrace tailWord_1232784 prefixEnd_1232784 422007156781606640420357 := by
  unfold tailWord_1232784
  simp only [CollatzResearch.WordTrace]
  refine ⟨22481663182920792795072703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29975550910561057060096937 22481663182920792795072703)
  ·
    refine ⟨33722494774381189192609055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22481663182920792795072703 33722494774381189192609055)
    ·
      refine ⟨50583742161571783788913583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33722494774381189192609055 50583742161571783788913583)
      ·
        refine ⟨75875613242357675683370375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50583742161571783788913583 75875613242357675683370375)
        ·
          refine ⟨113813419863536513525055563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75875613242357675683370375 113813419863536513525055563)
          ·
            refine ⟨170720129795304770287583345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113813419863536513525055563 170720129795304770287583345)
            ·
              refine ⟨128040097346478577715687509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170720129795304770287583345 128040097346478577715687509)
              ·
                refine ⟨1500469890779045832605713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 128040097346478577715687509 1500469890779045832605713)
                ·
                  refine ⟨1125352418084284374454285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1500469890779045832605713 1125352418084284374454285)
                  ·
                    refine ⟨422007156781606640420357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125352418084284374454285 422007156781606640420357)
                    ·
                      rfl

theorem cell22_1232784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 3].length) (baseStart_1232784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232784 prefixEnd_1232784 := by exact prefixLift 1232784
  have htrace : WordTrace (prefixWord ++ tailWord_1232784) baseStart_1232784 baseEnd_1232784 := by
    simpa [prefixWord, tailWord_1232784, baseEnd_1232784] using wordTrace_append hprefix tailTrace_1232784
  have hstable : (prefixWord ++ tailWord_1232784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232784).length < 2 ^ (prefixWord ++ tailWord_1232784).sum := by decide
  have hdescent : baseEnd_1232784 < baseStart_1232784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232801 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_1232801 : Nat := 118140960795 + 1232801 * 2 ^ 59
def prefixEnd_1232801 : Nat := 4983230072969 + 3 ^ 40 * 1232801 * 2
def baseEnd_1232801 : Nat := 422012976229024262745305

theorem tailTrace_1232801 : CollatzResearch.WordTrace tailWord_1232801 prefixEnd_1232801 422012976229024262745305 := by
  unfold tailWord_1232801
  simp only [CollatzResearch.WordTrace]
  refine ⟨44963946406779997493514257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29975964271186664995676171 44963946406779997493514257)
  ·
    refine ⟨33722959805084998120135693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44963946406779997493514257 33722959805084998120135693)
    ·
      refine ⟨12646109926906874295050885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33722959805084998120135693 12646109926906874295050885)
      ·
        refine ⟨2371145611295038930322041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12646109926906874295050885 2371145611295038930322041)
        ·
          refine ⟨1778359208471279197741531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2371145611295038930322041 1778359208471279197741531)
          ·
            refine ⟨2667538812706918796612297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778359208471279197741531 2667538812706918796612297)
            ·
              refine ⟨2000654109530189097459223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2667538812706918796612297 2000654109530189097459223)
              ·
                refine ⟨3000981164295283646188835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2000654109530189097459223 3000981164295283646188835)
                ·
                  refine ⟨4501471746442925469283253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3000981164295283646188835 4501471746442925469283253)
                  ·
                    refine ⟨422012976229024262745305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4501471746442925469283253 422012976229024262745305)
                    ·
                      rfl

theorem cell22_1232801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_1232801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232801 prefixEnd_1232801 := by exact prefixLift 1232801
  have htrace : WordTrace (prefixWord ++ tailWord_1232801) baseStart_1232801 baseEnd_1232801 := by
    simpa [prefixWord, tailWord_1232801, baseEnd_1232801] using wordTrace_append hprefix tailTrace_1232801
  have hstable : (prefixWord ++ tailWord_1232801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232801).length < 2 ^ (prefixWord ++ tailWord_1232801).sum := by decide
  have hdescent : baseEnd_1232801 < baseStart_1232801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232820 : List Nat := [2, 5, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1232820 : Nat := 118140960795 + 1232820 * 2 ^ 59
def prefixEnd_1232820 : Nat := 4983230072969 + 3 ^ 40 * 1232820 * 2
def baseEnd_1232820 : Nat := 140673160105771515506749

theorem tailTrace_1232820 : CollatzResearch.WordTrace tailWord_1232820 prefixEnd_1232820 140673160105771515506749 := by
  unfold tailWord_1232820
  simp only [CollatzResearch.WordTrace]
  refine ⟨22482319696855581869227957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29976426262474109158970609 22482319696855581869227957)
  ·
    refine ⟨2107717471580210800240121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22482319696855581869227957 2107717471580210800240121)
    ·
      refine ⟨1580788103685158100180091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2107717471580210800240121 1580788103685158100180091)
      ·
        refine ⟨2371182155527737150270137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1580788103685158100180091 2371182155527737150270137)
        ·
          refine ⟨1778386616645802862702603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2371182155527737150270137 1778386616645802862702603)
          ·
            refine ⟨2667579924968704294053905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778386616645802862702603 2667579924968704294053905)
            ·
              refine ⟨2000684943726528220540429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2667579924968704294053905 2000684943726528220540429)
              ·
                refine ⟨750256853897448082702661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2000684943726528220540429 750256853897448082702661)
                ·
                  refine ⟨140673160105771515506749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 750256853897448082702661 140673160105771515506749)
                  ·
                    rfl

theorem cell22_1232820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1232820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232820 prefixEnd_1232820 := by exact prefixLift 1232820
  have htrace : WordTrace (prefixWord ++ tailWord_1232820) baseStart_1232820 baseEnd_1232820 := by
    simpa [prefixWord, tailWord_1232820, baseEnd_1232820] using wordTrace_append hprefix tailTrace_1232820
  have hstable : (prefixWord ++ tailWord_1232820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232820).length < 2 ^ (prefixWord ++ tailWord_1232820).sum := by decide
  have hdescent : baseEnd_1232820 < baseStart_1232820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232846 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_1232846 : Nat := 118140960795 + 1232846 * 2 ^ 59
def prefixEnd_1232846 : Nat := 4983230072969 + 3 ^ 40 * 1232846 * 2
def baseEnd_1232846 : Nat := 422028380648659145370167

theorem tailTrace_1232846 : CollatzResearch.WordTrace tailWord_1232846 prefixEnd_1232846 422028380648659145370167 := by
  unfold tailWord_1232846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5620698461452121272362799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29977058461077980119268261 5620698461452121272362799)
  ·
    refine ⟨8431047692178181908544199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5620698461452121272362799 8431047692178181908544199)
    ·
      refine ⟨12646571538267272862816299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8431047692178181908544199 12646571538267272862816299)
      ·
        refine ⟨18969857307400909294224449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12646571538267272862816299 18969857307400909294224449)
        ·
          refine ⟨14227392980550681970668337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18969857307400909294224449 14227392980550681970668337)
          ·
            refine ⟨10670544735413011478001253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14227392980550681970668337 10670544735413011478001253)
            ·
              refine ⟨2000727137889939652125235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10670544735413011478001253 2000727137889939652125235)
              ·
                refine ⟨3001090706834909478187853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2000727137889939652125235 3001090706834909478187853)
                ·
                  refine ⟨1125409015063091054320445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3001090706834909478187853 1125409015063091054320445)
                  ·
                    refine ⟨422028380648659145370167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125409015063091054320445 422028380648659145370167)
                    ·
                      rfl

theorem cell22_1232846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_1232846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232846 prefixEnd_1232846 := by exact prefixLift 1232846
  have htrace : WordTrace (prefixWord ++ tailWord_1232846) baseStart_1232846 baseEnd_1232846 := by
    simpa [prefixWord, tailWord_1232846, baseEnd_1232846] using wordTrace_append hprefix tailTrace_1232846
  have hstable : (prefixWord ++ tailWord_1232846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232846).length < 2 ^ (prefixWord ++ tailWord_1232846).sum := by decide
  have hdescent : baseEnd_1232846 < baseStart_1232846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1232981 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_1232981 : Nat := 118140960795 + 1232981 * 2 ^ 59
def prefixEnd_1232981 : Nat := 4983230072969 + 3 ^ 40 * 1232981 * 2
def baseEnd_1232981 : Nat := 422074593907563793244753

theorem tailTrace_1232981 : CollatzResearch.WordTrace tailWord_1232981 prefixEnd_1232981 422074593907563793244753 := by
  unfold tailWord_1232981
  simp only [CollatzResearch.WordTrace]
  refine ⟨44970511546127888235066797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29980341030751925490044531 44970511546127888235066797)
  ·
    refine ⟨16863941829797958088150049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44970511546127888235066797 16863941829797958088150049)
    ·
      refine ⟨12647956372348468566112537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16863941829797958088150049 12647956372348468566112537)
      ·
        refine ⟨9485967279261351424584403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12647956372348468566112537 9485967279261351424584403)
        ·
          refine ⟨14228950918892027136876605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9485967279261351424584403 14228950918892027136876605)
          ·
            refine ⟨5335856594584510176328727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14228950918892027136876605 5335856594584510176328727)
            ·
              refine ⟨8003784891876765264493091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5335856594584510176328727 8003784891876765264493091)
              ·
                refine ⟨12005677337815147896739637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8003784891876765264493091 12005677337815147896739637)
                ·
                  refine ⟨1125532250420170115319341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12005677337815147896739637 1125532250420170115319341)
                  ·
                    refine ⟨422074593907563793244753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125532250420170115319341 422074593907563793244753)
                    ·
                      rfl

theorem cell22_1232981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_1232981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1232981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1232981 prefixEnd_1232981 := by exact prefixLift 1232981
  have htrace : WordTrace (prefixWord ++ tailWord_1232981) baseStart_1232981 baseEnd_1232981 := by
    simpa [prefixWord, tailWord_1232981, baseEnd_1232981] using wordTrace_append hprefix tailTrace_1232981
  have hstable : (prefixWord ++ tailWord_1232981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1232981).length < 2 ^ (prefixWord ++ tailWord_1232981).sum := by decide
  have hdescent : baseEnd_1232981 < baseStart_1232981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1232981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233009 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1233009 : Nat := 118140960795 + 1233009 * 2 ^ 59
def prefixEnd_1233009 : Nat := 4983230072969 + 3 ^ 40 * 1233009 * 2
def baseEnd_1233009 : Nat := 422084178879781053544667

theorem tailTrace_1233009 : CollatzResearch.WordTrace tailWord_1233009 prefixEnd_1233009 422084178879781053544667 := by
  unfold tailWord_1233009
  simp only [CollatzResearch.WordTrace]
  refine ⟨44971532790026449017086081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29981021860017632678057387 44971532790026449017086081)
  ·
    refine ⟨33728649592519836762814561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44971532790026449017086081 33728649592519836762814561)
    ·
      refine ⟨25296487194389877572110921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33728649592519836762814561 25296487194389877572110921)
      ·
        refine ⟨18972365395792408179083191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25296487194389877572110921 18972365395792408179083191)
        ·
          refine ⟨28458548093688612268624787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18972365395792408179083191 28458548093688612268624787)
          ·
            refine ⟨42687822140532918402937181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28458548093688612268624787 42687822140532918402937181)
            ·
              refine ⟨16007933302699844401101443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42687822140532918402937181 16007933302699844401101443)
              ·
                refine ⟨24011899954049766601652165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16007933302699844401101443 24011899954049766601652165)
                ·
                  refine ⟨4502231241384331237809781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24011899954049766601652165 4502231241384331237809781)
                  ·
                    refine ⟨422084178879781053544667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4502231241384331237809781 422084178879781053544667)
                    ·
                      rfl

theorem cell22_1233009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1233009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233009 prefixEnd_1233009 := by exact prefixLift 1233009
  have htrace : WordTrace (prefixWord ++ tailWord_1233009) baseStart_1233009 baseEnd_1233009 := by
    simpa [prefixWord, tailWord_1233009, baseEnd_1233009] using wordTrace_append hprefix tailTrace_1233009
  have hstable : (prefixWord ++ tailWord_1233009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233009).length < 2 ^ (prefixWord ++ tailWord_1233009).sum := by decide
  have hdescent : baseEnd_1233009 < baseStart_1233009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233028 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 5]
def baseStart_1233028 : Nat := 118140960795 + 1233028 * 2 ^ 59
def prefixEnd_1233028 : Nat := 4983230072969 + 3 ^ 40 * 1233028 * 2
def baseEnd_1233028 : Nat := 140696894322690445773203

theorem tailTrace_1233028 : CollatzResearch.WordTrace tailWord_1233028 prefixEnd_1233028 140696894322690445773203 := by
  unfold tailWord_1233028
  simp only [CollatzResearch.WordTrace]
  refine ⟨22486112888478807631013869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29981483851305076841351825 22486112888478807631013869)
  ·
    refine ⟨8432292333179552861630201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22486112888478807631013869 8432292333179552861630201)
    ·
      refine ⟨6324219249884664646222651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8432292333179552861630201 6324219249884664646222651)
      ·
        refine ⟨9486328874826996969333977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324219249884664646222651 9486328874826996969333977)
        ·
          refine ⟨7114746656120247727000483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9486328874826996969333977 7114746656120247727000483)
          ·
            refine ⟨10672119984180371590500725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7114746656120247727000483 10672119984180371590500725)
            ·
              refine ⟨1000511248516909836609443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10672119984180371590500725 1000511248516909836609443)
              ·
                refine ⟨1500766872775364754914165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000511248516909836609443 1500766872775364754914165)
                ·
                  refine ⟨140696894322690445773203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1500766872775364754914165 140696894322690445773203)
                  ·
                    rfl

theorem cell22_1233028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_1233028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233028 prefixEnd_1233028 := by exact prefixLift 1233028
  have htrace : WordTrace (prefixWord ++ tailWord_1233028) baseStart_1233028 baseEnd_1233028 := by
    simpa [prefixWord, tailWord_1233028, baseEnd_1233028] using wordTrace_append hprefix tailTrace_1233028
  have hstable : (prefixWord ++ tailWord_1233028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233028).length < 2 ^ (prefixWord ++ tailWord_1233028).sum := by decide
  have hdescent : baseEnd_1233028 < baseStart_1233028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233150 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1233150 : Nat := 118140960795 + 1233150 * 2 ^ 59
def prefixEnd_1233150 : Nat := 4983230072969 + 3 ^ 40 * 1233150 * 2
def baseEnd_1233150 : Nat := 422132446061303685769235

theorem tailTrace_1233150 : CollatzResearch.WordTrace tailWord_1233150 prefixEnd_1233150 422132446061303685769235 := by
  unfold tailWord_1233150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5622084435314453762246113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29984450321677086731979269 5622084435314453762246113)
  ·
    refine ⟨4216563326485840321684585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5622084435314453762246113 4216563326485840321684585)
    ·
      refine ⟨3162422494864380241263439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4216563326485840321684585 3162422494864380241263439)
      ·
        refine ⟨4743633742296570361895159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3162422494864380241263439 4743633742296570361895159)
        ·
          refine ⟨7115450613444855542842739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4743633742296570361895159 7115450613444855542842739)
          ·
            refine ⟨10673175920167283314264109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7115450613444855542842739 10673175920167283314264109)
            ·
              refine ⟨4002440970062731242849041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10673175920167283314264109 4002440970062731242849041)
              ·
                refine ⟨3001830727547048432136781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4002440970062731242849041 3001830727547048432136781)
                ·
                  refine ⟨1125686522830143162051293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3001830727547048432136781 1125686522830143162051293)
                  ·
                    refine ⟨422132446061303685769235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125686522830143162051293 422132446061303685769235)
                    ·
                      rfl

theorem cell22_1233150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1233150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233150 prefixEnd_1233150 := by exact prefixLift 1233150
  have htrace : WordTrace (prefixWord ++ tailWord_1233150) baseStart_1233150 baseEnd_1233150 := by
    simpa [prefixWord, tailWord_1233150, baseEnd_1233150] using wordTrace_append hprefix tailTrace_1233150
  have hstable : (prefixWord ++ tailWord_1233150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233150).length < 2 ^ (prefixWord ++ tailWord_1233150).sum := by decide
  have hdescent : baseEnd_1233150 < baseStart_1233150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233210 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_1233210 : Nat := 118140960795 + 1233210 * 2 ^ 59
def prefixEnd_1233210 : Nat := 4983230072969 + 3 ^ 40 * 1233210 * 2
def baseEnd_1233210 : Nat := 422152985287483529269051

theorem tailTrace_1233210 : CollatzResearch.WordTrace tailWord_1233210 prefixEnd_1233210 422152985287483529269051 := by
  unfold tailWord_1233210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244715965574565086288271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29985909241532173563435389 11244715965574565086288271)
  ·
    refine ⟨16867073948361847629432407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11244715965574565086288271 16867073948361847629432407)
    ·
      refine ⟨25300610922542771444148611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16867073948361847629432407 25300610922542771444148611)
      ·
        refine ⟨37950916383814157166222917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25300610922542771444148611 37950916383814157166222917)
        ·
          refine ⟨7115796821965154468666797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37950916383814157166222917 7115796821965154468666797)
          ·
            refine ⟨2668423808236932925750049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7115796821965154468666797 2668423808236932925750049)
            ·
              refine ⟨2001317856177699694312537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2668423808236932925750049 2001317856177699694312537)
              ·
                refine ⟨1500988392133274770734403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001317856177699694312537 1500988392133274770734403)
                ·
                  refine ⟨2251482588199912156101605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500988392133274770734403 2251482588199912156101605)
                  ·
                    refine ⟨422152985287483529269051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2251482588199912156101605 422152985287483529269051)
                    ·
                      rfl

theorem cell22_1233210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_1233210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233210 prefixEnd_1233210 := by exact prefixLift 1233210
  have htrace : WordTrace (prefixWord ++ tailWord_1233210) baseStart_1233210 baseEnd_1233210 := by
    simpa [prefixWord, tailWord_1233210, baseEnd_1233210] using wordTrace_append hprefix tailTrace_1233210
  have hstable : (prefixWord ++ tailWord_1233210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233210).length < 2 ^ (prefixWord ++ tailWord_1233210).sum := by decide
  have hdescent : baseEnd_1233210 < baseStart_1233210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233223 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1233223 : Nat := 118140960795 + 1233223 * 2 ^ 59
def prefixEnd_1233223 : Nat := 4983230072969 + 3 ^ 40 * 1233223 * 2
def baseEnd_1233223 : Nat := 422157435453155828694011

theorem tailTrace_1233223 : CollatzResearch.WordTrace tailWord_1233223 prefixEnd_1233223 422157435453155828694011 := by
  unfold tailWord_1233223
  simp only [CollatzResearch.WordTrace]
  refine ⟨44979338011251163565376323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29986225340834109043584215 44979338011251163565376323)
  ·
    refine ⟨67469007016876745348064485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44979338011251163565376323 67469007016876745348064485)
    ·
      refine ⟨12650438815664389752762091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67469007016876745348064485 12650438815664389752762091)
      ·
        refine ⟨18975658223496584629143137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12650438815664389752762091 18975658223496584629143137)
        ·
          refine ⟨14231743667622438471857353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18975658223496584629143137 14231743667622438471857353)
          ·
            refine ⟨10673807750716828853893015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14231743667622438471857353 10673807750716828853893015)
            ·
              refine ⟨16010711626075243280839523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10673807750716828853893015 16010711626075243280839523)
              ·
                refine ⟨24016067439112864921259285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16010711626075243280839523 24016067439112864921259285)
                ·
                  refine ⟨1125753161208415543184029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24016067439112864921259285 1125753161208415543184029)
                  ·
                    refine ⟨422157435453155828694011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125753161208415543184029 422157435453155828694011)
                    ·
                      rfl

theorem cell22_1233223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1233223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233223 prefixEnd_1233223 := by exact prefixLift 1233223
  have htrace : WordTrace (prefixWord ++ tailWord_1233223) baseStart_1233223 baseEnd_1233223 := by
    simpa [prefixWord, tailWord_1233223, baseEnd_1233223] using wordTrace_append hprefix tailTrace_1233223
  have hstable : (prefixWord ++ tailWord_1233223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233223).length < 2 ^ (prefixWord ++ tailWord_1233223).sum := by decide
  have hdescent : baseEnd_1233223 < baseStart_1233223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233253 : List Nat := [1, 3, 1, 3, 1, 4, 2, 7]
def baseStart_1233253 : Nat := 118140960795 + 1233253 * 2 ^ 59
def prefixEnd_1233253 : Nat := 4983230072969 + 3 ^ 40 * 1233253 * 2
def baseEnd_1233253 : Nat := 46907522785138416715991

theorem tailTrace_1233253 : CollatzResearch.WordTrace tailWord_1233253 prefixEnd_1233253 46907522785138416715991 := by
  unfold tailWord_1233253
  simp only [CollatzResearch.WordTrace]
  refine ⟨44980432201142478688968413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29986954800761652459312275 44980432201142478688968413)
  ·
    refine ⟨16867662075428429508363155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44980432201142478688968413 16867662075428429508363155)
    ·
      refine ⟨25301493113142644262544733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16867662075428429508363155 25301493113142644262544733)
      ·
        refine ⟨9488059917428491598454275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25301493113142644262544733 9488059917428491598454275)
        ·
          refine ⟨14232089876142737397681413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9488059917428491598454275 14232089876142737397681413)
          ·
            refine ⟨2668516851776763262065265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14232089876142737397681413 2668516851776763262065265)
            ·
              refine ⟨2001387638832572446548949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2668516851776763262065265 2001387638832572446548949)
              ·
                refine ⟨46907522785138416715991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2001387638832572446548949 46907522785138416715991)
                ·
                  rfl

theorem cell22_1233253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 7].length) (baseStart_1233253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233253 prefixEnd_1233253 := by exact prefixLift 1233253
  have htrace : WordTrace (prefixWord ++ tailWord_1233253) baseStart_1233253 baseEnd_1233253 := by
    simpa [prefixWord, tailWord_1233253, baseEnd_1233253] using wordTrace_append hprefix tailTrace_1233253
  have hstable : (prefixWord ++ tailWord_1233253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233253).length < 2 ^ (prefixWord ++ tailWord_1233253).sum := by decide
  have hdescent : baseEnd_1233253 < baseStart_1233253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233375 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 1, 5]
def baseStart_1233375 : Nat := 118140960795 + 1233375 * 2 ^ 59
def prefixEnd_1233375 : Nat := 4983230072969 + 3 ^ 40 * 1233375 * 2
def baseEnd_1233375 : Nat := 422209468159478098893545

theorem tailTrace_1233375 : CollatzResearch.WordTrace tailWord_1233375 prefixEnd_1233375 422209468159478098893545 := by
  unfold tailWord_1233375
  simp only [CollatzResearch.WordTrace]
  refine ⟨44984881906700493524909579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29989921271133662349939719 44984881906700493524909579)
  ·
    refine ⟨67477322860050740287364369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44984881906700493524909579 67477322860050740287364369)
    ·
      refine ⟨50607992145038055215523277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67477322860050740287364369 50607992145038055215523277)
      ·
        refine ⟨18977997054389270705821229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50607992145038055215523277 18977997054389270705821229)
        ·
          refine ⟨7116748895395976514682961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18977997054389270705821229 7116748895395976514682961)
          ·
            refine ⟨5337561671546982386012221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7116748895395976514682961 5337561671546982386012221)
            ·
              refine ⟨2001585626830118394754583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5337561671546982386012221 2001585626830118394754583)
              ·
                refine ⟨3002378440245177592131875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001585626830118394754583 3002378440245177592131875)
                ·
                  refine ⟨4503567660367766388197813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3002378440245177592131875 4503567660367766388197813)
                  ·
                    refine ⟨422209468159478098893545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4503567660367766388197813 422209468159478098893545)
                    ·
                      rfl

theorem cell22_1233375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_1233375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233375 prefixEnd_1233375 := by exact prefixLift 1233375
  have htrace : WordTrace (prefixWord ++ tailWord_1233375) baseStart_1233375 baseEnd_1233375 := by
    simpa [prefixWord, tailWord_1233375, baseEnd_1233375] using wordTrace_append hprefix tailTrace_1233375
  have hstable : (prefixWord ++ tailWord_1233375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233375).length < 2 ^ (prefixWord ++ tailWord_1233375).sum := by decide
  have hdescent : baseEnd_1233375 < baseStart_1233375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233388 : List Nat := [2, 2, 1, 1, 2, 1, 5, 8]
def baseStart_1233388 : Nat := 118140960795 + 1233388 * 2 ^ 59
def prefixEnd_1233388 : Nat := 4983230072969 + 3 ^ 40 * 1233388 * 2
def baseEnd_1233388 : Nat := 46912657591683377590945

theorem tailTrace_1233388 : CollatzResearch.WordTrace tailWord_1233388 prefixEnd_1233388 46912657591683377590945 := by
  unfold tailWord_1233388
  simp only [CollatzResearch.WordTrace]
  refine ⟨22492678027826698372566409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29990237370435597830088545 22492678027826698372566409)
  ·
    refine ⟨16869508520870023779424807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22492678027826698372566409 16869508520870023779424807)
    ·
      refine ⟨25304262781305035669137211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16869508520870023779424807 25304262781305035669137211)
      ·
        refine ⟨37956394171957553503705817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25304262781305035669137211 37956394171957553503705817)
        ·
          refine ⟨28467295628968165127779363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37956394171957553503705817 28467295628968165127779363)
          ·
            refine ⟨42700943443452247691669045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28467295628968165127779363 42700943443452247691669045)
            ·
              refine ⟨4003213447823648221093973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42700943443452247691669045 4003213447823648221093973)
              ·
                refine ⟨46912657591683377590945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4003213447823648221093973 46912657591683377590945)
                ·
                  rfl

theorem cell22_1233388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 8].length) (baseStart_1233388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233388 prefixEnd_1233388 := by exact prefixLift 1233388
  have htrace : WordTrace (prefixWord ++ tailWord_1233388) baseStart_1233388 baseEnd_1233388 := by
    simpa [prefixWord, tailWord_1233388, baseEnd_1233388] using wordTrace_append hprefix tailTrace_1233388
  have hstable : (prefixWord ++ tailWord_1233388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233388).length < 2 ^ (prefixWord ++ tailWord_1233388).sum := by decide
  have hdescent : baseEnd_1233388 < baseStart_1233388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233390 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1233390 : Nat := 118140960795 + 1233390 * 2 ^ 59
def prefixEnd_1233390 : Nat := 4983230072969 + 3 ^ 40 * 1233390 * 2
def baseEnd_1233390 : Nat := 422214602966023059768499

theorem tailTrace_1233390 : CollatzResearch.WordTrace tailWord_1233390 prefixEnd_1233390 422214602966023059768499 := by
  unfold tailWord_1233390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5623178625205768885838203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29990286001097434057803749 5623178625205768885838203)
  ·
    refine ⟨8434767937808653328757305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5623178625205768885838203 8434767937808653328757305)
    ·
      refine ⟨6326075953356489996567979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8434767937808653328757305 6326075953356489996567979)
      ·
        refine ⟨9489113930034734994851969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6326075953356489996567979 9489113930034734994851969)
        ·
          refine ⟨7116835447526051246138977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9489113930034734994851969 7116835447526051246138977)
          ·
            refine ⟨5337626585644538434604233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7116835447526051246138977 5337626585644538434604233)
            ·
              refine ⟨4003219939233403825953175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5337626585644538434604233 4003219939233403825953175)
              ·
                refine ⟨6004829908850105738929763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4003219939233403825953175 6004829908850105738929763)
                ·
                  refine ⟨9007244863275158608394645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6004829908850105738929763 9007244863275158608394645)
                  ·
                    refine ⟨422214602966023059768499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9007244863275158608394645 422214602966023059768499)
                    ·
                      rfl

theorem cell22_1233390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1233390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233390 prefixEnd_1233390 := by exact prefixLift 1233390
  have htrace : WordTrace (prefixWord ++ tailWord_1233390) baseStart_1233390 baseEnd_1233390 := by
    simpa [prefixWord, tailWord_1233390, baseEnd_1233390] using wordTrace_append hprefix tailTrace_1233390
  have hstable : (prefixWord ++ tailWord_1233390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233390).length < 2 ^ (prefixWord ++ tailWord_1233390).sum := by decide
  have hdescent : baseEnd_1233390 < baseStart_1233390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233465 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_1233465 : Nat := 118140960795 + 1233465 * 2 ^ 59
def prefixEnd_1233465 : Nat := 4983230072969 + 3 ^ 40 * 1233465 * 2
def baseEnd_1233465 : Nat := 422240276998747864143269

theorem tailTrace_1233465 : CollatzResearch.WordTrace tailWord_1233465 prefixEnd_1233465 422240276998747864143269 := by
  unfold tailWord_1233465
  simp only [CollatzResearch.WordTrace]
  refine ⟨44988164476374438895685849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29992109650916292597123899 44988164476374438895685849)
  ·
    refine ⟨33741123357280829171764387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44988164476374438895685849 33741123357280829171764387)
    ·
      refine ⟨50611685035921243757646581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33741123357280829171764387 50611685035921243757646581)
      ·
        refine ⟨4744845472117616602279367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50611685035921243757646581 4744845472117616602279367)
        ·
          refine ⟨7117268208176424903419051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4744845472117616602279367 7117268208176424903419051)
          ·
            refine ⟨10675902312264637355128577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7117268208176424903419051 10675902312264637355128577)
            ·
              refine ⟨8006926734198478016346433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10675902312264637355128577 8006926734198478016346433)
              ·
                refine ⟨6005195050648858512259825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8006926734198478016346433 6005195050648858512259825)
                ·
                  refine ⟨4503896287986643884194869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005195050648858512259825 4503896287986643884194869)
                  ·
                    refine ⟨422240276998747864143269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4503896287986643884194869 422240276998747864143269)
                    ·
                      rfl

theorem cell22_1233465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_1233465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233465 prefixEnd_1233465 := by exact prefixLift 1233465
  have htrace : WordTrace (prefixWord ++ tailWord_1233465) baseStart_1233465 baseEnd_1233465 := by
    simpa [prefixWord, tailWord_1233465, baseEnd_1233465] using wordTrace_append hprefix tailTrace_1233465
  have hstable : (prefixWord ++ tailWord_1233465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233465).length < 2 ^ (prefixWord ++ tailWord_1233465).sum := by decide
  have hdescent : baseEnd_1233465 < baseStart_1233465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233495 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 6]
def baseStart_1233495 : Nat := 118140960795 + 1233495 * 2 ^ 59
def prefixEnd_1233495 : Nat := 4983230072969 + 3 ^ 40 * 1233495 * 2
def baseEnd_1233495 : Nat := 140750182203945928631059

theorem tailTrace_1233495 : CollatzResearch.WordTrace tailWord_1233495 prefixEnd_1233495 140750182203945928631059 := by
  unfold tailWord_1233495
  simp only [CollatzResearch.WordTrace]
  refine ⟨44989258666265754019277939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29992839110843836012851959 44989258666265754019277939)
  ·
    refine ⟨67483887999398631028916909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44989258666265754019277939 67483887999398631028916909)
    ·
      refine ⟨25306457999774486635843841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67483887999398631028916909 25306457999774486635843841)
      ·
        refine ⟨18979843499830864976882881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25306457999774486635843841 18979843499830864976882881)
        ·
          refine ⟨14234882624873148732662161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18979843499830864976882881 14234882624873148732662161)
          ·
            refine ⟨10676161968654861549496621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14234882624873148732662161 10676161968654861549496621)
            ·
              refine ⟨4003560738245573081061233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10676161968654861549496621 4003560738245573081061233)
              ·
                refine ⟨3002670553684179810795925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003560738245573081061233 3002670553684179810795925)
                ·
                  refine ⟨140750182203945928631059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3002670553684179810795925 140750182203945928631059)
                  ·
                    rfl

theorem cell22_1233495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 6].length) (baseStart_1233495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233495 prefixEnd_1233495 := by exact prefixLift 1233495
  have htrace : WordTrace (prefixWord ++ tailWord_1233495) baseStart_1233495 baseEnd_1233495 := by
    simpa [prefixWord, tailWord_1233495, baseEnd_1233495] using wordTrace_append hprefix tailTrace_1233495
  have hstable : (prefixWord ++ tailWord_1233495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233495).length < 2 ^ (prefixWord ++ tailWord_1233495).sum := by decide
  have hdescent : baseEnd_1233495 < baseStart_1233495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233640 : List Nat := [2, 1, 4, 1, 4, 2, 2, 2, 1, 3]
def baseStart_1233640 : Nat := 118140960795 + 1233640 * 2 ^ 59
def prefixEnd_1233640 : Nat := 4983230072969 + 3 ^ 40 * 1233640 * 2
def baseEnd_1233640 : Nat := 422300183075105741017733

theorem tailTrace_1233640 : CollatzResearch.WordTrace tailWord_1233640 prefixEnd_1233640 422300183075105741017733 := by
  unfold tailWord_1233640
  simp only [CollatzResearch.WordTrace]
  refine ⟨22497273625370221891653187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29996364833826962522204249 22497273625370221891653187)
  ·
    refine ⟨33745910438055332837479781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22497273625370221891653187 33745910438055332837479781)
    ·
      refine ⟨6327358207135374907027459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33745910438055332837479781 6327358207135374907027459)
      ·
        refine ⟨9491037310703062360541189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6327358207135374907027459 9491037310703062360541189)
        ·
          refine ⟨1779569495756824192601473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9491037310703062360541189 1779569495756824192601473)
          ·
            refine ⟨1334677121817618144451105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1779569495756824192601473 1334677121817618144451105)
            ·
              refine ⟨1001007841363213608338329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334677121817618144451105 1001007841363213608338329)
              ·
                refine ⟨750755881022410206253747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001007841363213608338329 750755881022410206253747)
                ·
                  refine ⟨1126133821533615309380621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750755881022410206253747 1126133821533615309380621)
                  ·
                    refine ⟨422300183075105741017733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1126133821533615309380621 422300183075105741017733)
                    ·
                      rfl

theorem cell22_1233640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_1233640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233640 prefixEnd_1233640 := by exact prefixLift 1233640
  have htrace : WordTrace (prefixWord ++ tailWord_1233640) baseStart_1233640 baseEnd_1233640 := by
    simpa [prefixWord, tailWord_1233640, baseEnd_1233640] using wordTrace_append hprefix tailTrace_1233640
  have hstable : (prefixWord ++ tailWord_1233640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233640).length < 2 ^ (prefixWord ++ tailWord_1233640).sum := by decide
  have hdescent : baseEnd_1233640 < baseStart_1233640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233692 : List Nat := [2, 2, 3, 1, 1, 4, 9]
def baseStart_1233692 : Nat := 118140960795 + 1233692 * 2 ^ 59
def prefixEnd_1233692 : Nat := 4983230072969 + 3 ^ 40 * 1233692 * 2
def baseEnd_1233692 : Nat := 15641406805103516248799

theorem tailTrace_1233692 : CollatzResearch.WordTrace tailWord_1233692 prefixEnd_1233692 15641406805103516248799 := by
  unfold tailWord_1233692
  simp only [CollatzResearch.WordTrace]
  refine ⟨22498221923276028332099665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29997629231034704442799553 22498221923276028332099665)
  ·
    refine ⟨16873666442457021249074749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22498221923276028332099665 16873666442457021249074749)
    ·
      refine ⟨6327624915921382968403031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16873666442457021249074749 6327624915921382968403031)
      ·
        refine ⟨9491437373882074452604547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6327624915921382968403031 9491437373882074452604547)
        ·
          refine ⟨14237156060823111678906821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9491437373882074452604547 14237156060823111678906821)
          ·
            refine ⟨2669466761404333439795029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14237156060823111678906821 2669466761404333439795029)
            ·
              refine ⟨15641406805103516248799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2669466761404333439795029 15641406805103516248799)
              ·
                rfl

theorem cell22_1233692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 9].length) (baseStart_1233692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233692 prefixEnd_1233692 := by exact prefixLift 1233692
  have htrace : WordTrace (prefixWord ++ tailWord_1233692) baseStart_1233692 baseEnd_1233692 := by
    simpa [prefixWord, tailWord_1233692, baseEnd_1233692] using wordTrace_append hprefix tailTrace_1233692
  have hstable : (prefixWord ++ tailWord_1233692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233692).length < 2 ^ (prefixWord ++ tailWord_1233692).sum := by decide
  have hdescent : baseEnd_1233692 < baseStart_1233692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233696 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 2, 3]
def baseStart_1233696 : Nat := 118140960795 + 1233696 * 2 ^ 59
def prefixEnd_1233696 : Nat := 4983230072969 + 3 ^ 40 * 1233696 * 2
def baseEnd_1233696 : Nat := 422319353019540261617561

theorem tailTrace_1233696 : CollatzResearch.WordTrace tailWord_1233696 prefixEnd_1233696 422319353019540261617561 := by
  unfold tailWord_1233696
  simp only [CollatzResearch.WordTrace]
  refine ⟨22498294869268782673672471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29997726492358376898229961 22498294869268782673672471)
  ·
    refine ⟨33747442303903174010508707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22498294869268782673672471 33747442303903174010508707)
    ·
      refine ⟨50621163455854761015763061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33747442303903174010508707 50621163455854761015763061)
      ·
        refine ⟨4745734073986383845227787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50621163455854761015763061 4745734073986383845227787)
        ·
          refine ⟨7118601110979575767841681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4745734073986383845227787 7118601110979575767841681)
          ·
            refine ⟨5338950833234681825881261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7118601110979575767841681 5338950833234681825881261)
            ·
              refine ⟨2002106562463005684705473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5338950833234681825881261 2002106562463005684705473)
              ·
                refine ⟨1501579921847254263529105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002106562463005684705473 1501579921847254263529105)
                ·
                  refine ⟨1126184941385440697646829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1501579921847254263529105 1126184941385440697646829)
                  ·
                    refine ⟨422319353019540261617561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1126184941385440697646829 422319353019540261617561)
                    ·
                      rfl

theorem cell22_1233696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 3].length) (baseStart_1233696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233696 prefixEnd_1233696 := by exact prefixLift 1233696
  have htrace : WordTrace (prefixWord ++ tailWord_1233696) baseStart_1233696 baseEnd_1233696 := by
    simpa [prefixWord, tailWord_1233696, baseEnd_1233696] using wordTrace_append hprefix tailTrace_1233696
  have hstable : (prefixWord ++ tailWord_1233696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233696).length < 2 ^ (prefixWord ++ tailWord_1233696).sum := by decide
  have hdescent : baseEnd_1233696 < baseStart_1233696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233732 : List Nat := [2, 3, 4, 2, 2, 1, 1, 3, 4]
def baseStart_1233732 : Nat := 118140960795 + 1233732 * 2 ^ 59
def prefixEnd_1233732 : Nat := 4983230072969 + 3 ^ 40 * 1233732 * 2
def baseEnd_1233732 : Nat := 140777225518416055905817

theorem tailTrace_1233732 : CollatzResearch.WordTrace tailWord_1233732 prefixEnd_1233732 140777225518416055905817 := by
  unfold tailWord_1233732
  simp only [CollatzResearch.WordTrace]
  refine ⟨22498951383203571747827725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29998601844271428997103633 22498951383203571747827725)
  ·
    refine ⟨8437106768701339405435397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22498951383203571747827725 8437106768701339405435397)
    ·
      refine ⟨1581957519131501138519137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8437106768701339405435397 1581957519131501138519137)
      ·
        refine ⟨1186468139348625853889353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1581957519131501138519137 1186468139348625853889353)
        ·
          refine ⟨889851104511469390417015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186468139348625853889353 889851104511469390417015)
          ·
            refine ⟨1334776656767204085625523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889851104511469390417015 1334776656767204085625523)
            ·
              refine ⟨2002164985150806128438285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334776656767204085625523 2002164985150806128438285)
              ·
                refine ⟨750811869431552298164357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2002164985150806128438285 750811869431552298164357)
                ·
                  refine ⟨140777225518416055905817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 750811869431552298164357 140777225518416055905817)
                  ·
                    rfl

theorem cell22_1233732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_1233732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233732 prefixEnd_1233732 := by exact prefixLift 1233732
  have htrace : WordTrace (prefixWord ++ tailWord_1233732) baseStart_1233732 baseEnd_1233732 := by
    simpa [prefixWord, tailWord_1233732, baseEnd_1233732] using wordTrace_append hprefix tailTrace_1233732
  have hstable : (prefixWord ++ tailWord_1233732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233732).length < 2 ^ (prefixWord ++ tailWord_1233732).sum := by decide
  have hdescent : baseEnd_1233732 < baseStart_1233732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233737 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 7]
def baseStart_1233737 : Nat := 118140960795 + 1233737 * 2 ^ 59
def prefixEnd_1233737 : Nat := 4983230072969 + 3 ^ 40 * 1233737 * 2
def baseEnd_1233737 : Nat := 140777796052476607114145

theorem tailTrace_1233737 : CollatzResearch.WordTrace tailWord_1233737 prefixEnd_1233737 140777796052476607114145 := by
  unfold tailWord_1233737
  simp only [CollatzResearch.WordTrace]
  refine ⟨44998085131389029349587465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29998723420926019566391643 44998085131389029349587465)
  ·
    refine ⟨33748563848541772012190599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44998085131389029349587465 33748563848541772012190599)
    ·
      refine ⟨50622845772812658018285899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33748563848541772012190599 50622845772812658018285899)
      ·
        refine ⟨75934268659218987027428849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50622845772812658018285899 75934268659218987027428849)
        ·
          refine ⟨56950701494414240270571637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75934268659218987027428849 56950701494414240270571637)
          ·
            refine ⟨5339128265101335025366091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56950701494414240270571637 5339128265101335025366091)
            ·
              refine ⟨8008692397652002538049137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339128265101335025366091 8008692397652002538049137)
              ·
                refine ⟨6006519298239001903536853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8008692397652002538049137 6006519298239001903536853)
                ·
                  refine ⟨140777796052476607114145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6006519298239001903536853 140777796052476607114145)
                  ·
                    rfl

theorem cell22_1233737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_1233737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233737 prefixEnd_1233737 := by exact prefixLift 1233737
  have htrace : WordTrace (prefixWord ++ tailWord_1233737) baseStart_1233737 baseEnd_1233737 := by
    simpa [prefixWord, tailWord_1233737, baseEnd_1233737] using wordTrace_append hprefix tailTrace_1233737
  have hstable : (prefixWord ++ tailWord_1233737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233737).length < 2 ^ (prefixWord ++ tailWord_1233737).sum := by decide
  have hdescent : baseEnd_1233737 < baseStart_1233737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233752 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1233752 : Nat := 118140960795 + 1233752 * 2 ^ 59
def prefixEnd_1233752 : Nat := 4983230072969 + 3 ^ 40 * 1233752 * 2
def baseEnd_1233752 : Nat := 422338522963974782217389

theorem tailTrace_1233752 : CollatzResearch.WordTrace tailWord_1233752 prefixEnd_1233752 422338522963974782217389 := by
  unfold tailWord_1233752
  simp only [CollatzResearch.WordTrace]
  refine ⟨22499316113167343455691755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29999088150889791274255673 22499316113167343455691755)
  ·
    refine ⟨33748974169751015183537633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22499316113167343455691755 33748974169751015183537633)
    ·
      refine ⟨25311730627313261387653225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33748974169751015183537633 25311730627313261387653225)
      ·
        refine ⟨18983797970484946040739919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25311730627313261387653225 18983797970484946040739919)
        ·
          refine ⟨28475696955727419061109879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18983797970484946040739919 28475696955727419061109879)
          ·
            refine ⟨42713545433591128591664819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28475696955727419061109879 42713545433591128591664819)
            ·
              refine ⟨64070318150386692887497229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42713545433591128591664819 64070318150386692887497229)
              ·
                refine ⟨24026369306395009832811461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64070318150386692887497229 24026369306395009832811461)
                ·
                  refine ⟨4504944244949064343652149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24026369306395009832811461 4504944244949064343652149)
                  ·
                    refine ⟨422338522963974782217389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4504944244949064343652149 422338522963974782217389)
                    ·
                      rfl

theorem cell22_1233752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1233752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233752 prefixEnd_1233752 := by exact prefixLift 1233752
  have htrace : WordTrace (prefixWord ++ tailWord_1233752) baseStart_1233752 baseEnd_1233752 := by
    simpa [prefixWord, tailWord_1233752, baseEnd_1233752] using wordTrace_append hprefix tailTrace_1233752
  have hstable : (prefixWord ++ tailWord_1233752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233752).length < 2 ^ (prefixWord ++ tailWord_1233752).sum := by decide
  have hdescent : baseEnd_1233752 < baseStart_1233752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233784 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_1233784 : Nat := 118140960795 + 1233784 * 2 ^ 59
def prefixEnd_1233784 : Nat := 4983230072969 + 3 ^ 40 * 1233784 * 2
def baseEnd_1233784 : Nat := 422349477217937365417291

theorem tailTrace_1233784 : CollatzResearch.WordTrace tailWord_1233784 prefixEnd_1233784 422349477217937365417291 := by
  unfold tailWord_1233784
  simp only [CollatzResearch.WordTrace]
  refine ⟨22499899681109378188274203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29999866241479170917698937 22499899681109378188274203)
  ·
    refine ⟨33749849521664067282411305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22499899681109378188274203 33749849521664067282411305)
    ·
      refine ⟨25312387141248050461808479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33749849521664067282411305 25312387141248050461808479)
      ·
        refine ⟨37968580711872075692712719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25312387141248050461808479 37968580711872075692712719)
        ·
          refine ⟨56952871067808113539069079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37968580711872075692712719 56952871067808113539069079)
          ·
            refine ⟨85429306601712170308603619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56952871067808113539069079 85429306601712170308603619)
            ·
              refine ⟨128143959902568255462905429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85429306601712170308603619 128143959902568255462905429)
              ·
                refine ⟨1501687030108221743705923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 128143959902568255462905429 1501687030108221743705923)
                ·
                  refine ⟨2252530545162332615558885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501687030108221743705923 2252530545162332615558885)
                  ·
                    refine ⟨422349477217937365417291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2252530545162332615558885 422349477217937365417291)
                    ·
                      rfl

theorem cell22_1233784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_1233784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233784 prefixEnd_1233784 := by exact prefixLift 1233784
  have htrace : WordTrace (prefixWord ++ tailWord_1233784) baseStart_1233784 baseEnd_1233784 := by
    simpa [prefixWord, tailWord_1233784, baseEnd_1233784] using wordTrace_append hprefix tailTrace_1233784
  have hstable : (prefixWord ++ tailWord_1233784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233784).length < 2 ^ (prefixWord ++ tailWord_1233784).sum := by decide
  have hdescent : baseEnd_1233784 < baseStart_1233784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233919 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 7, 4]
def baseStart_1233919 : Nat := 118140960795 + 1233919 * 2 ^ 59
def prefixEnd_1233919 : Nat := 4983230072969 + 3 ^ 40 * 1233919 * 2
def baseEnd_1233919 : Nat := 422395690476842013291877

theorem tailTrace_1233919 : CollatzResearch.WordTrace tailWord_1233919 prefixEnd_1233919 422395690476842013291877 := by
  unfold tailWord_1233919
  simp only [CollatzResearch.WordTrace]
  refine ⟨45004723216729674432712811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30003148811153116288475207 45004723216729674432712811)
  ·
    refine ⟨67507084825094511649069217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45004723216729674432712811 67507084825094511649069217)
    ·
      refine ⟨50630313618820883736801913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67507084825094511649069217 50630313618820883736801913)
      ·
        refine ⟨37972735214115662802601435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50630313618820883736801913 37972735214115662802601435)
        ·
          refine ⟨56959102821173494203902153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37972735214115662802601435 56959102821173494203902153)
          ·
            refine ⟨42719327115880120652926615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56959102821173494203902153 42719327115880120652926615)
            ·
              refine ⟨64078990673820180979389923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42719327115880120652926615 64078990673820180979389923)
              ·
                refine ⟨96118486010730271469084885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64078990673820180979389923 96118486010730271469084885)
                ·
                  refine ⟨2252777015876490737556677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 96118486010730271469084885 2252777015876490737556677)
                  ·
                    refine ⟨422395690476842013291877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2252777015876490737556677 422395690476842013291877)
                    ·
                      rfl

theorem cell22_1233919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_1233919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233919 prefixEnd_1233919 := by exact prefixLift 1233919
  have htrace : WordTrace (prefixWord ++ tailWord_1233919) baseStart_1233919 baseEnd_1233919 := by
    simpa [prefixWord, tailWord_1233919, baseEnd_1233919] using wordTrace_append hprefix tailTrace_1233919
  have hstable : (prefixWord ++ tailWord_1233919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233919).length < 2 ^ (prefixWord ++ tailWord_1233919).sum := by decide
  have hdescent : baseEnd_1233919 < baseStart_1233919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233953 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_1233953 : Nat := 118140960795 + 1233953 * 2 ^ 59
def prefixEnd_1233953 : Nat := 4983230072969 + 3 ^ 40 * 1233953 * 2
def baseEnd_1233953 : Nat := 422407329371677257941773

theorem tailTrace_1233953 : CollatzResearch.WordTrace tailWord_1233953 prefixEnd_1233953 422407329371677257941773 := by
  unfold tailWord_1233953
  simp only [CollatzResearch.WordTrace]
  refine ⟨45005963298606498239450513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30003975532404332159633675 45005963298606498239450513)
  ·
    refine ⟨33754472473954873679587885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45005963298606498239450513 33754472473954873679587885)
    ·
      refine ⟨12657927177733077629845457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33754472473954873679587885 12657927177733077629845457)
      ·
        refine ⟨9493445383299808222384093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12657927177733077629845457 9493445383299808222384093)
        ·
          refine ⟨3560042018737428083394035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9493445383299808222384093 3560042018737428083394035)
          ·
            refine ⟨5340063028106142125091053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560042018737428083394035 5340063028106142125091053)
            ·
              refine ⟨2002523635539803296909145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5340063028106142125091053 2002523635539803296909145)
              ·
                refine ⟨1501892726654852472681859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002523635539803296909145 1501892726654852472681859)
                ·
                  refine ⟨2252839089982278709022789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501892726654852472681859 2252839089982278709022789)
                  ·
                    refine ⟨422407329371677257941773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2252839089982278709022789 422407329371677257941773)
                    ·
                      rfl

theorem cell22_1233953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_1233953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233953 prefixEnd_1233953 := by exact prefixLift 1233953
  have htrace : WordTrace (prefixWord ++ tailWord_1233953) baseStart_1233953 baseEnd_1233953 := by
    simpa [prefixWord, tailWord_1233953, baseEnd_1233953] using wordTrace_append hprefix tailTrace_1233953
  have hstable : (prefixWord ++ tailWord_1233953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233953).length < 2 ^ (prefixWord ++ tailWord_1233953).sum := by decide
  have hdescent : baseEnd_1233953 < baseStart_1233953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1233985 : List Nat := [1, 2, 5, 1, 3, 1, 1, 4, 4]
def baseStart_1233985 : Nat := 118140960795 + 1233985 * 2 ^ 59
def prefixEnd_1233985 : Nat := 4983230072969 + 3 ^ 40 * 1233985 * 2
def baseEnd_1233985 : Nat := 140806094541879947047225

theorem tailTrace_1233985 : CollatzResearch.WordTrace tailWord_1233985 prefixEnd_1233985 140806094541879947047225 := by
  unfold tailWord_1233985
  simp only [CollatzResearch.WordTrace]
  refine ⟨45007130434490567704615409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30004753622993711803076939 45007130434490567704615409)
  ·
    refine ⟨33755347825867925778461557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45007130434490567704615409 33755347825867925778461557)
    ·
      refine ⟨3164563858675118041730771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33755347825867925778461557 3164563858675118041730771)
      ·
        refine ⟨4746845788012677062596157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3164563858675118041730771 4746845788012677062596157)
        ·
          refine ⟨1780067170504753898473559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4746845788012677062596157 1780067170504753898473559)
          ·
            refine ⟨2670100755757130847710339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780067170504753898473559 2670100755757130847710339)
            ·
              refine ⟨4005151133635696271565509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670100755757130847710339 4005151133635696271565509)
              ·
                refine ⟨750965837556693050918533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4005151133635696271565509 750965837556693050918533)
                ·
                  refine ⟨140806094541879947047225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 750965837556693050918533 140806094541879947047225)
                  ·
                    rfl

theorem cell22_1233985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 4].length) (baseStart_1233985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1233985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1233985 prefixEnd_1233985 := by exact prefixLift 1233985
  have htrace : WordTrace (prefixWord ++ tailWord_1233985) baseStart_1233985 baseEnd_1233985 := by
    simpa [prefixWord, tailWord_1233985, baseEnd_1233985] using wordTrace_append hprefix tailTrace_1233985
  have hstable : (prefixWord ++ tailWord_1233985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1233985).length < 2 ^ (prefixWord ++ tailWord_1233985).sum := by decide
  have hdescent : baseEnd_1233985 < baseStart_1233985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1233985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234045 : List Nat := [1, 4, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_1234045 : Nat := 118140960795 + 1234045 * 2 ^ 59
def prefixEnd_1234045 : Nat := 4983230072969 + 3 ^ 40 * 1234045 * 2
def baseEnd_1234045 : Nat := 422438822851819684641491

theorem tailTrace_1234045 : CollatzResearch.WordTrace tailWord_1234045 prefixEnd_1234045 422438822851819684641491 := by
  unfold tailWord_1234045
  simp only [CollatzResearch.WordTrace]
  refine ⟨45009318814273197951799589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30006212542848798634533059 45009318814273197951799589)
  ·
    refine ⟨8439247277676224615962423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45009318814273197951799589 8439247277676224615962423)
    ·
      refine ⟨12658870916514336923943635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8439247277676224615962423 12658870916514336923943635)
      ·
        refine ⟨18988306374771505385915453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12658870916514336923943635 18988306374771505385915453)
        ·
          refine ⟨7120614890539314519718295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18988306374771505385915453 7120614890539314519718295)
          ·
            refine ⟨10680922335808971779577443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7120614890539314519718295 10680922335808971779577443)
            ·
              refine ⟨16021383503713457669366165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10680922335808971779577443 16021383503713457669366165)
              ·
                refine ⟨751002351736568328251539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16021383503713457669366165 751002351736568328251539)
                ·
                  refine ⟨1126503527604852492377309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751002351736568328251539 1126503527604852492377309)
                  ·
                    refine ⟨422438822851819684641491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1126503527604852492377309 422438822851819684641491)
                    ·
                      rfl

theorem cell22_1234045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_1234045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234045 prefixEnd_1234045 := by exact prefixLift 1234045
  have htrace : WordTrace (prefixWord ++ tailWord_1234045) baseStart_1234045 baseEnd_1234045 := by
    simpa [prefixWord, tailWord_1234045, baseEnd_1234045] using wordTrace_append hprefix tailTrace_1234045
  have hstable : (prefixWord ++ tailWord_1234045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234045).length < 2 ^ (prefixWord ++ tailWord_1234045).sum := by decide
  have hdescent : baseEnd_1234045 < baseStart_1234045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234079 : List Nat := [1, 1, 2, 6, 2, 2, 1, 3, 1, 3]
def baseStart_1234079 : Nat := 118140960795 + 1234079 * 2 ^ 59
def prefixEnd_1234079 : Nat := 4983230072969 + 3 ^ 40 * 1234079 * 2
def baseEnd_1234079 : Nat := 422450461746654929291387

theorem tailTrace_1234079 : CollatzResearch.WordTrace tailWord_1234079 prefixEnd_1234079 422450461746654929291387 := by
  unfold tailWord_1234079
  simp only [CollatzResearch.WordTrace]
  refine ⟨45010558896150021758537291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30007039264100014505691527 45010558896150021758537291)
  ·
    refine ⟨67515838344225032637805937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45010558896150021758537291 67515838344225032637805937)
    ·
      refine ⟨50636878758168774478354453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67515838344225032637805937 50636878758168774478354453)
      ·
        refine ⟨2373603691789161303672865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50636878758168774478354453 2373603691789161303672865)
        ·
          refine ⟨1780202768841870977754649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2373603691789161303672865 1780202768841870977754649)
          ·
            refine ⟨1335152076631403233315987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780202768841870977754649 1335152076631403233315987)
            ·
              refine ⟨2002728114947104849973981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335152076631403233315987 2002728114947104849973981)
              ·
                refine ⟨751023043105164318740243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2002728114947104849973981 751023043105164318740243)
                ·
                  refine ⟨1126534564657746478110365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751023043105164318740243 1126534564657746478110365)
                  ·
                    refine ⟨422450461746654929291387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1126534564657746478110365 422450461746654929291387)
                    ·
                      rfl

theorem cell22_1234079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 1, 3].length) (baseStart_1234079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234079 prefixEnd_1234079 := by exact prefixLift 1234079
  have htrace : WordTrace (prefixWord ++ tailWord_1234079) baseStart_1234079 baseEnd_1234079 := by
    simpa [prefixWord, tailWord_1234079, baseEnd_1234079] using wordTrace_append hprefix tailTrace_1234079
  have hstable : (prefixWord ++ tailWord_1234079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234079).length < 2 ^ (prefixWord ++ tailWord_1234079).sum := by decide
  have hdescent : baseEnd_1234079 < baseStart_1234079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234176 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 9]
def baseStart_1234176 : Nat := 118140960795 + 1234176 * 2 ^ 59
def prefixEnd_1234176 : Nat := 4983230072969 + 3 ^ 40 * 1234176 * 2
def baseEnd_1234176 : Nat := 140827888942993003205363

theorem tailTrace_1234176 : CollatzResearch.WordTrace tailWord_1234176 prefixEnd_1234176 140827888942993003205363 := by
  unfold tailWord_1234176
  simp only [CollatzResearch.WordTrace]
  refine ⟨22507048388399303662409191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30009397851199071549878921 22507048388399303662409191)
  ·
    refine ⟨33760572582598955493613787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22507048388399303662409191 33760572582598955493613787)
    ·
      refine ⟨50640858873898433240420681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33760572582598955493613787 50640858873898433240420681)
      ·
        refine ⟨37980644155423824930315511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50640858873898433240420681 37980644155423824930315511)
        ·
          refine ⟨56970966233135737395473267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37980644155423824930315511 56970966233135737395473267)
          ·
            refine ⟨85456449349703606093209901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56970966233135737395473267 85456449349703606093209901)
            ·
              refine ⟨32046168506138852284953713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85456449349703606093209901 32046168506138852284953713)
              ·
                refine ⟨24034626379604139213715285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32046168506138852284953713 24034626379604139213715285)
                ·
                  refine ⟨140827888942993003205363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24034626379604139213715285 140827888942993003205363)
                  ·
                    rfl

theorem cell22_1234176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_1234176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234176 prefixEnd_1234176 := by exact prefixLift 1234176
  have htrace : WordTrace (prefixWord ++ tailWord_1234176) baseStart_1234176 baseEnd_1234176 := by
    simpa [prefixWord, tailWord_1234176, baseEnd_1234176] using wordTrace_append hprefix tailTrace_1234176
  have hstable : (prefixWord ++ tailWord_1234176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234176).length < 2 ^ (prefixWord ++ tailWord_1234176).sum := by decide
  have hdescent : baseEnd_1234176 < baseStart_1234176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234180 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_1234180 : Nat := 118140960795 + 1234180 * 2 ^ 59
def prefixEnd_1234180 : Nat := 4983230072969 + 3 ^ 40 * 1234180 * 2
def baseEnd_1234180 : Nat := 422485036110724332516077

theorem tailTrace_1234180 : CollatzResearch.WordTrace tailWord_1234180 prefixEnd_1234180 422485036110724332516077 := by
  unfold tailWord_1234180
  simp only [CollatzResearch.WordTrace]
  refine ⟨22507121334392058003981997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30009495112522744005309329 22507121334392058003981997)
  ·
    refine ⟨8440170500397021751493249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22507121334392058003981997 8440170500397021751493249)
    ·
      refine ⟨6330127875297766313619937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8440170500397021751493249 6330127875297766313619937)
      ·
        refine ⟨4747595906473324735214953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6330127875297766313619937 4747595906473324735214953)
        ·
          refine ⟨3560696929854993551411215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4747595906473324735214953 3560696929854993551411215)
          ·
            refine ⟨5341045394782490327116823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560696929854993551411215 5341045394782490327116823)
            ·
              refine ⟨8011568092173735490675235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5341045394782490327116823 8011568092173735490675235)
              ·
                refine ⟨12017352138260603236012853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8011568092173735490675235 12017352138260603236012853)
                ·
                  refine ⟨1126626762961931553376205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12017352138260603236012853 1126626762961931553376205)
                  ·
                    refine ⟨422485036110724332516077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1126626762961931553376205 422485036110724332516077)
                    ·
                      rfl

theorem cell22_1234180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_1234180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234180 prefixEnd_1234180 := by exact prefixLift 1234180
  have htrace : WordTrace (prefixWord ++ tailWord_1234180) baseStart_1234180 baseEnd_1234180 := by
    simpa [prefixWord, tailWord_1234180, baseEnd_1234180] using wordTrace_append hprefix tailTrace_1234180
  have hstable : (prefixWord ++ tailWord_1234180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234180).length < 2 ^ (prefixWord ++ tailWord_1234180).sum := by decide
  have hdescent : baseEnd_1234180 < baseStart_1234180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234210 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1234210 : Nat := 118140960795 + 1234210 * 2 ^ 59
def prefixEnd_1234210 : Nat := 4983230072969 + 3 ^ 40 * 1234210 * 2
def baseEnd_1234210 : Nat := 140831768574604751421995

theorem tailTrace_1234210 : CollatzResearch.WordTrace tailWord_1234210 prefixEnd_1234210 140831768574604751421995 := by
  unfold tailWord_1234210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11253834214668857782889021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30010224572450287421037389 11253834214668857782889021)
  ·
    refine ⟨4220187830500821668583383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11253834214668857782889021 4220187830500821668583383)
    ·
      refine ⟨6330281745751232502875075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4220187830500821668583383 6330281745751232502875075)
      ·
        refine ⟨9495422618626848754312613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6330281745751232502875075 9495422618626848754312613)
        ·
          refine ⟨1780391740992534141433615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9495422618626848754312613 1780391740992534141433615)
          ·
            refine ⟨2670587611488801212150423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780391740992534141433615 2670587611488801212150423)
            ·
              refine ⟨4005881417233201818225635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670587611488801212150423 4005881417233201818225635)
              ·
                refine ⟨6008822125849802727338453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4005881417233201818225635 6008822125849802727338453)
                ·
                  refine ⟨140831768574604751421995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6008822125849802727338453 140831768574604751421995)
                  ·
                    rfl

theorem cell22_1234210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1234210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234210 prefixEnd_1234210 := by exact prefixLift 1234210
  have htrace : WordTrace (prefixWord ++ tailWord_1234210) baseStart_1234210 baseEnd_1234210 := by
    simpa [prefixWord, tailWord_1234210, baseEnd_1234210] using wordTrace_append hprefix tailTrace_1234210
  have hstable : (prefixWord ++ tailWord_1234210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234210).length < 2 ^ (prefixWord ++ tailWord_1234210).sum := by decide
  have hdescent : baseEnd_1234210 < baseStart_1234210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234240 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_1234240 : Nat := 118140960795 + 1234240 * 2 ^ 59
def prefixEnd_1234240 : Nat := 4983230072969 + 3 ^ 40 * 1234240 * 2
def baseEnd_1234240 : Nat := 422505575336904176015893

theorem tailTrace_1234240 : CollatzResearch.WordTrace tailWord_1234240 prefixEnd_1234240 422505575336904176015893 := by
  unfold tailWord_1234240
  simp only [CollatzResearch.WordTrace]
  refine ⟨22508215524283373127574087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30010954032377830836765449 22508215524283373127574087)
  ·
    refine ⟨33762323286425059691361131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22508215524283373127574087 33762323286425059691361131)
    ·
      refine ⟨50643484929637589537041697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33762323286425059691361131 50643484929637589537041697)
      ·
        refine ⟨37982613697228192152781273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50643484929637589537041697 37982613697228192152781273)
        ·
          refine ⟨28486960272921144114585955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37982613697228192152781273 28486960272921144114585955)
          ·
            refine ⟨42730440409381716171878933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28486960272921144114585955 42730440409381716171878933)
            ·
              refine ⟨2002989394189767945556825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42730440409381716171878933 2002989394189767945556825)
              ·
                refine ⟨1502242045642325959167619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2002989394189767945556825 1502242045642325959167619)
                ·
                  refine ⟨2253363068463488938751429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502242045642325959167619 2253363068463488938751429)
                  ·
                    refine ⟨422505575336904176015893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2253363068463488938751429 422505575336904176015893)
                    ·
                      rfl

theorem cell22_1234240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_1234240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234240 prefixEnd_1234240 := by exact prefixLift 1234240
  have htrace : WordTrace (prefixWord ++ tailWord_1234240) baseStart_1234240 baseEnd_1234240 := by
    simpa [prefixWord, tailWord_1234240, baseEnd_1234240] using wordTrace_append hprefix tailTrace_1234240
  have hstable : (prefixWord ++ tailWord_1234240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234240).length < 2 ^ (prefixWord ++ tailWord_1234240).sum := by decide
  have hdescent : baseEnd_1234240 < baseStart_1234240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234334 : List Nat := [4, 3, 1, 2, 2, 2, 1, 7]
def baseStart_1234334 : Nat := 118140960795 + 1234334 * 2 ^ 59
def prefixEnd_1234334 : Nat := 4983230072969 + 3 ^ 40 * 1234334 * 2
def baseEnd_1234334 : Nat := 46948639273102140462845

theorem tailTrace_1234334 : CollatzResearch.WordTrace tailWord_1234334 prefixEnd_1234334 46948639273102140462845 := by
  unfold tailWord_1234334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627482438778275038633757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30013239673484133539380037 5627482438778275038633757)
  ·
    refine ⟨2110305914541853139487659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5627482438778275038633757 2110305914541853139487659)
    ·
      refine ⟨3165458871812779709231489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2110305914541853139487659 3165458871812779709231489)
      ·
        refine ⟨2374094153859584781923617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3165458871812779709231489 2374094153859584781923617)
        ·
          refine ⟨1780570615394688586442713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2374094153859584781923617 1780570615394688586442713)
          ·
            refine ⟨1335427961546016439832035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780570615394688586442713 1335427961546016439832035)
            ·
              refine ⟨2003141942319024659748053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335427961546016439832035 2003141942319024659748053)
              ·
                refine ⟨46948639273102140462845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2003141942319024659748053 46948639273102140462845)
                ·
                  rfl

theorem cell22_1234334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_1234334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234334 prefixEnd_1234334 := by exact prefixLift 1234334
  have htrace : WordTrace (prefixWord ++ tailWord_1234334) baseStart_1234334 baseEnd_1234334 := by
    simpa [prefixWord, tailWord_1234334, baseEnd_1234334] using wordTrace_append hprefix tailTrace_1234334
  have hstable : (prefixWord ++ tailWord_1234334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234334).length < 2 ^ (prefixWord ++ tailWord_1234334).sum := by decide
  have hdescent : baseEnd_1234334 < baseStart_1234334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234349 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1234349 : Nat := 118140960795 + 1234349 * 2 ^ 59
def prefixEnd_1234349 : Nat := 4983230072969 + 3 ^ 40 * 1234349 * 2
def baseEnd_1234349 : Nat := 422542888264464225040559

theorem tailTrace_1234349 : CollatzResearch.WordTrace tailWord_1234349 prefixEnd_1234349 422542888264464225040559 := by
  unfold tailWord_1234349
  simp only [CollatzResearch.WordTrace]
  refine ⟨45020406605171857870866101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30013604403447905247244067 45020406605171857870866101)
  ·
    refine ⟨4220663119234861675393697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45020406605171857870866101 4220663119234861675393697)
    ·
      refine ⟨3165497339426146256545273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4220663119234861675393697 3165497339426146256545273)
      ·
        refine ⟨2374123004569609692408955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3165497339426146256545273 2374123004569609692408955)
        ·
          refine ⟨3561184506854414538613433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374123004569609692408955 3561184506854414538613433)
          ·
            refine ⟨2670888380140810903960075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3561184506854414538613433 2670888380140810903960075)
            ·
              refine ⟨4006332570211216355940113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670888380140810903960075 4006332570211216355940113)
              ·
                refine ⟨3004749427658412266955085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4006332570211216355940113 3004749427658412266955085)
                ·
                  refine ⟨1126781035371904600108157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3004749427658412266955085 1126781035371904600108157)
                  ·
                    refine ⟨422542888264464225040559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1126781035371904600108157 422542888264464225040559)
                    ·
                      rfl

theorem cell22_1234349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1234349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234349 prefixEnd_1234349 := by exact prefixLift 1234349
  have htrace : WordTrace (prefixWord ++ tailWord_1234349) baseStart_1234349 baseEnd_1234349 := by
    simpa [prefixWord, tailWord_1234349, baseEnd_1234349] using wordTrace_append hprefix tailTrace_1234349
  have hstable : (prefixWord ++ tailWord_1234349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234349).length < 2 ^ (prefixWord ++ tailWord_1234349).sum := by decide
  have hdescent : baseEnd_1234349 < baseStart_1234349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234424 : List Nat := [2, 1, 2, 1, 1, 7, 1, 3, 4]
def baseStart_1234424 : Nat := 118140960795 + 1234424 * 2 ^ 59
def prefixEnd_1234424 : Nat := 4983230072969 + 3 ^ 40 * 1234424 * 2
def baseEnd_1234424 : Nat := 140856187432396343138443

theorem tailTrace_1234424 : CollatzResearch.WordTrace tailWord_1234424 prefixEnd_1234424 140856187432396343138443 := by
  unfold tailWord_1234424
  simp only [CollatzResearch.WordTrace]
  refine ⟨22511571039950072839923163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30015428053266763786564217 22511571039950072839923163)
  ·
    refine ⟨33767356559925109259884745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22511571039950072839923163 33767356559925109259884745)
    ·
      refine ⟨25325517419943831944913559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33767356559925109259884745 25325517419943831944913559)
      ·
        refine ⟨37988276129915747917370339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25325517419943831944913559 37988276129915747917370339)
        ·
          refine ⟨56982414194873621876055509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37988276129915747917370339 56982414194873621876055509)
          ·
            refine ⟨1335525332692350512720051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 56982414194873621876055509 1335525332692350512720051)
            ·
              refine ⟨2003287999038525769080077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335525332692350512720051 2003287999038525769080077)
              ·
                refine ⟨751232999639447163405029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2003287999038525769080077 751232999639447163405029)
                ·
                  refine ⟨140856187432396343138443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 751232999639447163405029 140856187432396343138443)
                  ·
                    rfl

theorem cell22_1234424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 4].length) (baseStart_1234424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234424 prefixEnd_1234424 := by exact prefixLift 1234424
  have htrace : WordTrace (prefixWord ++ tailWord_1234424) baseStart_1234424 baseEnd_1234424 := by
    simpa [prefixWord, tailWord_1234424, baseEnd_1234424] using wordTrace_append hprefix tailTrace_1234424
  have hstable : (prefixWord ++ tailWord_1234424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234424).length < 2 ^ (prefixWord ++ tailWord_1234424).sum := by decide
  have hdescent : baseEnd_1234424 < baseStart_1234424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234544 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 1, 4]
def baseStart_1234544 : Nat := 118140960795 + 1234544 * 2 ^ 59
def prefixEnd_1234544 : Nat := 4983230072969 + 3 ^ 40 * 1234544 * 2
def baseEnd_1234544 : Nat := 422609640749548716414961

theorem tailTrace_1234544 : CollatzResearch.WordTrace tailWord_1234544 prefixEnd_1234544 422609640749548716414961 := by
  unfold tailWord_1234544
  simp only [CollatzResearch.WordTrace]
  refine ⟨22513759419732703087107343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30018345892976937449476457 22513759419732703087107343)
  ·
    refine ⟨33770639129599054630661015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22513759419732703087107343 33770639129599054630661015)
    ·
      refine ⟨50655958694398581945991523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33770639129599054630661015 50655958694398581945991523)
      ·
        refine ⟨75983938041597872918987285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50655958694398581945991523 75983938041597872918987285)
        ·
          refine ⟨3561747095699900293077529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75983938041597872918987285 3561747095699900293077529)
          ·
            refine ⟨2671310321774925219808147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3561747095699900293077529 2671310321774925219808147)
            ·
              refine ⟨4006965482662387829712221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671310321774925219808147 4006965482662387829712221)
              ·
                refine ⟨1502612055998395436142083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4006965482662387829712221 1502612055998395436142083)
                ·
                  refine ⟨2253918083997593154213125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502612055998395436142083 2253918083997593154213125)
                  ·
                    refine ⟨422609640749548716414961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2253918083997593154213125 422609640749548716414961)
                    ·
                      rfl

theorem cell22_1234544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 4].length) (baseStart_1234544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234544 prefixEnd_1234544 := by exact prefixLift 1234544
  have htrace : WordTrace (prefixWord ++ tailWord_1234544) baseStart_1234544 baseEnd_1234544 := by
    simpa [prefixWord, tailWord_1234544, baseEnd_1234544] using wordTrace_append hprefix tailTrace_1234544
  have hstable : (prefixWord ++ tailWord_1234544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234544).length < 2 ^ (prefixWord ++ tailWord_1234544).sum := by decide
  have hdescent : baseEnd_1234544 < baseStart_1234544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234574 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_1234574 : Nat := 118140960795 + 1234574 * 2 ^ 59
def prefixEnd_1234574 : Nat := 4983230072969 + 3 ^ 40 * 1234574 * 2
def baseEnd_1234574 : Nat := 422619910362638638164869

theorem tailTrace_1234574 : CollatzResearch.WordTrace tailWord_1234574 prefixEnd_1234574 422619910362638638164869 := by
  unfold tailWord_1234574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628576628669590162225847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30019075352904480865204517 5628576628669590162225847)
  ·
    refine ⟨8442864943004385243338771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5628576628669590162225847 8442864943004385243338771)
    ·
      refine ⟨12664297414506577865008157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8442864943004385243338771 12664297414506577865008157)
      ·
        refine ⟨4749111530439966699378059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12664297414506577865008157 4749111530439966699378059)
        ·
          refine ⟨7123667295659950049067089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4749111530439966699378059 7123667295659950049067089)
          ·
            refine ⟨5342750471744962536800317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7123667295659950049067089 5342750471744962536800317)
            ·
              refine ⟨2003531426904360951300119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5342750471744962536800317 2003531426904360951300119)
              ·
                refine ⟨3005297140356541426950179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003531426904360951300119 3005297140356541426950179)
                ·
                  refine ⟨4507945710534812140425269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005297140356541426950179 4507945710534812140425269)
                  ·
                    refine ⟨422619910362638638164869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4507945710534812140425269 422619910362638638164869)
                    ·
                      rfl

theorem cell22_1234574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_1234574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234574 prefixEnd_1234574 := by exact prefixLift 1234574
  have htrace : WordTrace (prefixWord ++ tailWord_1234574) baseStart_1234574 baseEnd_1234574 := by
    simpa [prefixWord, tailWord_1234574, baseEnd_1234574] using wordTrace_append hprefix tailTrace_1234574
  have hstable : (prefixWord ++ tailWord_1234574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234574).length < 2 ^ (prefixWord ++ tailWord_1234574).sum := by decide
  have hdescent : baseEnd_1234574 < baseStart_1234574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234709 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1234709 : Nat := 118140960795 + 1234709 * 2 ^ 59
def prefixEnd_1234709 : Nat := 4983230072969 + 3 ^ 40 * 1234709 * 2
def baseEnd_1234709 : Nat := 422666123621543286039455

theorem tailTrace_1234709 : CollatzResearch.WordTrace tailWord_1234709 prefixEnd_1234709 422666123621543286039455 := by
  unfold tailWord_1234709
  simp only [CollatzResearch.WordTrace]
  refine ⟨45033536883867639353971181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30022357922578426235980787 45033536883867639353971181)
  ·
    refine ⟨16887576331450364757739193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45033536883867639353971181 16887576331450364757739193)
    ·
      refine ⟨12665682248587773568304395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16887576331450364757739193 12665682248587773568304395)
      ·
        refine ⟨18998523372881660352456593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12665682248587773568304395 18998523372881660352456593)
        ·
          refine ⟨14248892529661245264342445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18998523372881660352456593 14248892529661245264342445)
          ·
            refine ⟨5343334698622966974128417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14248892529661245264342445 5343334698622966974128417)
            ·
              refine ⟨4007501023967225230596313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5343334698622966974128417 4007501023967225230596313)
              ·
                refine ⟨3005625767975418922947235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4007501023967225230596313 3005625767975418922947235)
                ·
                  refine ⟨4508438651963128384420853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005625767975418922947235 4508438651963128384420853)
                  ·
                    refine ⟨422666123621543286039455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4508438651963128384420853 422666123621543286039455)
                    ·
                      rfl

theorem cell22_1234709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1234709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234709 prefixEnd_1234709 := by exact prefixLift 1234709
  have htrace : WordTrace (prefixWord ++ tailWord_1234709) baseStart_1234709 baseEnd_1234709 := by
    simpa [prefixWord, tailWord_1234709, baseEnd_1234709] using wordTrace_append hprefix tailTrace_1234709
  have hstable : (prefixWord ++ tailWord_1234709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234709).length < 2 ^ (prefixWord ++ tailWord_1234709).sum := by decide
  have hdescent : baseEnd_1234709 < baseStart_1234709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234711 : List Nat := [1, 1, 3, 4, 2, 1, 1, 5, 4]
def baseStart_1234711 : Nat := 118140960795 + 1234711 * 2 ^ 59
def prefixEnd_1234711 : Nat := 4983230072969 + 3 ^ 40 * 1234711 * 2
def baseEnd_1234711 : Nat := 140888936087471982496483

theorem tailTrace_1234711 : CollatzResearch.WordTrace tailWord_1234711 prefixEnd_1234711 140888936087471982496483 := by
  unfold tailWord_1234711
  simp only [CollatzResearch.WordTrace]
  refine ⟨45033609829860393695543987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30022406553240262463695991 45033609829860393695543987)
  ·
    refine ⟨67550414744790590543315981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45033609829860393695543987 67550414744790590543315981)
    ·
      refine ⟨25331405529296471453743493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67550414744790590543315981 25331405529296471453743493)
      ·
        refine ⟨4749638536743088397576905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25331405529296471453743493 4749638536743088397576905)
        ·
          refine ⟨3562228902557316298182679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4749638536743088397576905 3562228902557316298182679)
          ·
            refine ⟨5343343353835974447274019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562228902557316298182679 5343343353835974447274019)
            ·
              refine ⟨8015015030753961670911029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5343343353835974447274019 8015015030753961670911029)
              ·
                refine ⟨751407659133183906647909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8015015030753961670911029 751407659133183906647909)
                ·
                  refine ⟨140888936087471982496483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 751407659133183906647909 140888936087471982496483)
                  ·
                    rfl

theorem cell22_1234711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 4].length) (baseStart_1234711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234711 prefixEnd_1234711 := by exact prefixLift 1234711
  have htrace : WordTrace (prefixWord ++ tailWord_1234711) baseStart_1234711 baseEnd_1234711 := by
    simpa [prefixWord, tailWord_1234711, baseEnd_1234711] using wordTrace_append hprefix tailTrace_1234711
  have hstable : (prefixWord ++ tailWord_1234711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234711).length < 2 ^ (prefixWord ++ tailWord_1234711).sum := by decide
  have hdescent : baseEnd_1234711 < baseStart_1234711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234758 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1234758 : Nat := 118140960795 + 1234758 * 2 ^ 59
def prefixEnd_1234758 : Nat := 4983230072969 + 3 ^ 40 * 1234758 * 2
def baseEnd_1234758 : Nat := 422682897322923491564305

theorem tailTrace_1234758 : CollatzResearch.WordTrace tailWord_1234758 prefixEnd_1234758 422682897322923491564305 := by
  unfold tailWord_1234758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1407353876896566272578279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30023549373793413815003285 1407353876896566272578279)
  ·
    refine ⟨2111030815344849408867419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1407353876896566272578279 2111030815344849408867419)
    ·
      refine ⟨3166546223017274113301129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2111030815344849408867419 3166546223017274113301129)
      ·
        refine ⟨2374909667262955584975847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3166546223017274113301129 2374909667262955584975847)
        ·
          refine ⟨3562364500894433377463771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374909667262955584975847 3562364500894433377463771)
          ·
            refine ⟨5343546751341650066195657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562364500894433377463771 5343546751341650066195657)
            ·
              refine ⟨4007660063506237549646743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5343546751341650066195657 4007660063506237549646743)
              ·
                refine ⟨6011490095259356324470115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4007660063506237549646743 6011490095259356324470115)
                ·
                  refine ⟨9017235142889034486705173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6011490095259356324470115 9017235142889034486705173)
                  ·
                    refine ⟨422682897322923491564305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9017235142889034486705173 422682897322923491564305)
                    ·
                      rfl

theorem cell22_1234758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1234758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234758 prefixEnd_1234758 := by exact prefixLift 1234758
  have htrace : WordTrace (prefixWord ++ tailWord_1234758) baseStart_1234758 baseEnd_1234758 := by
    simpa [prefixWord, tailWord_1234758, baseEnd_1234758] using wordTrace_append hprefix tailTrace_1234758
  have hstable : (prefixWord ++ tailWord_1234758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234758).length < 2 ^ (prefixWord ++ tailWord_1234758).sum := by decide
  have hdescent : baseEnd_1234758 < baseStart_1234758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234784 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 7]
def baseStart_1234784 : Nat := 118140960795 + 1234784 * 2 ^ 59
def prefixEnd_1234784 : Nat := 4983230072969 + 3 ^ 40 * 1234784 * 2
def baseEnd_1234784 : Nat := 140897265884756030138075

theorem tailTrace_1234784 : CollatzResearch.WordTrace tailWord_1234784 prefixEnd_1234784 140897265884756030138075 := by
  unfold tailWord_1234784
  simp only [CollatzResearch.WordTrace]
  refine ⟨22518136179297963581475703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30024181572397284775300937 22518136179297963581475703)
  ·
    refine ⟨33777204268946945372213555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22518136179297963581475703 33777204268946945372213555)
    ·
      refine ⟨50665806403420418058320333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33777204268946945372213555 50665806403420418058320333)
      ·
        refine ⟨18999677401282656771870125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50665806403420418058320333 18999677401282656771870125)
        ·
          refine ⟨7124879025480996289451297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18999677401282656771870125 7124879025480996289451297)
          ·
            refine ⟨5343659269110747217088473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7124879025480996289451297 5343659269110747217088473)
            ·
              refine ⟨4007744451833060412816355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5343659269110747217088473 4007744451833060412816355)
              ·
                refine ⟨6011616677749590619224533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4007744451833060412816355 6011616677749590619224533)
                ·
                  refine ⟨140897265884756030138075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6011616677749590619224533 140897265884756030138075)
                  ·
                    rfl

theorem cell22_1234784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_1234784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234784 prefixEnd_1234784 := by exact prefixLift 1234784
  have htrace : WordTrace (prefixWord ++ tailWord_1234784) baseStart_1234784 baseEnd_1234784 := by
    simpa [prefixWord, tailWord_1234784, baseEnd_1234784] using wordTrace_append hprefix tailTrace_1234784
  have hstable : (prefixWord ++ tailWord_1234784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234784).length < 2 ^ (prefixWord ++ tailWord_1234784).sum := by decide
  have hdescent : baseEnd_1234784 < baseStart_1234784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234794 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 2, 3]
def baseStart_1234794 : Nat := 118140960795 + 1234794 * 2 ^ 59
def prefixEnd_1234794 : Nat := 4983230072969 + 3 ^ 40 * 1234794 * 2
def baseEnd_1234794 : Nat := 422695220858631397664195

theorem tailTrace_1234794 : CollatzResearch.WordTrace tailWord_1234794 prefixEnd_1234794 422695220858631397664195 := by
  unfold tailWord_1234794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259159272139924717703859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30024424725706465913876957 11259159272139924717703859)
  ·
    refine ⟨16888738908209887076555789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11259159272139924717703859 16888738908209887076555789)
    ·
      refine ⟨6333277090578707653708421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16888738908209887076555789 6333277090578707653708421)
      ·
        refine ⟨1187489454483507685070329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6333277090578707653708421 1187489454483507685070329)
        ·
          refine ⟨890617090862630763802747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1187489454483507685070329 890617090862630763802747)
          ·
            refine ⟨1335925636293946145704121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890617090862630763802747 1335925636293946145704121)
            ·
              refine ⟨1001944227220459609278091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1335925636293946145704121 1001944227220459609278091)
              ·
                refine ⟨1502916340830689413917137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001944227220459609278091 1502916340830689413917137)
                ·
                  refine ⟨1127187255623017060437853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1502916340830689413917137 1127187255623017060437853)
                  ·
                    refine ⟨422695220858631397664195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1127187255623017060437853 422695220858631397664195)
                    ·
                      rfl

theorem cell22_1234794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_1234794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234794 prefixEnd_1234794 := by exact prefixLift 1234794
  have htrace : WordTrace (prefixWord ++ tailWord_1234794) baseStart_1234794 baseEnd_1234794 := by
    simpa [prefixWord, tailWord_1234794, baseEnd_1234794] using wordTrace_append hprefix tailTrace_1234794
  have hstable : (prefixWord ++ tailWord_1234794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234794).length < 2 ^ (prefixWord ++ tailWord_1234794).sum := by decide
  have hdescent : baseEnd_1234794 < baseStart_1234794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1234970 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_1234970 : Nat := 118140960795 + 1234970 * 2 ^ 59
def prefixEnd_1234970 : Nat := 4983230072969 + 3 ^ 40 * 1234970 * 2
def baseEnd_1234970 : Nat := 140918489751808535087885

theorem tailTrace_1234970 : CollatzResearch.WordTrace tailWord_1234970 prefixEnd_1234970 140918489751808535087885 := by
  unfold tailWord_1234970
  simp only [CollatzResearch.WordTrace]
  refine ⟨11260764083980520232305591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30028704223948053952814909 11260764083980520232305591)
  ·
    refine ⟨16891146125970780348458387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11260764083980520232305591 16891146125970780348458387)
    ·
      refine ⟨25336719188956170522687581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16891146125970780348458387 25336719188956170522687581)
      ·
        refine ⟨9501269695858563946007843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25336719188956170522687581 9501269695858563946007843)
        ·
          refine ⟨14251904543787845919011765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9501269695858563946007843 14251904543787845919011765)
          ·
            refine ⟨1336116050980110554907353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14251904543787845919011765 1336116050980110554907353)
            ·
              refine ⟨1002087038235082916180515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336116050980110554907353 1002087038235082916180515)
              ·
                refine ⟨1503130557352624374270773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002087038235082916180515 1503130557352624374270773)
                ·
                  refine ⟨140918489751808535087885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1503130557352624374270773 140918489751808535087885)
                  ·
                    rfl

theorem cell22_1234970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_1234970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1234970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1234970 prefixEnd_1234970 := by exact prefixLift 1234970
  have htrace : WordTrace (prefixWord ++ tailWord_1234970) baseStart_1234970 baseEnd_1234970 := by
    simpa [prefixWord, tailWord_1234970, baseEnd_1234970] using wordTrace_append hprefix tailTrace_1234970
  have hstable : (prefixWord ++ tailWord_1234970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1234970).length < 2 ^ (prefixWord ++ tailWord_1234970).sum := by decide
  have hdescent : baseEnd_1234970 < baseStart_1234970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1234970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235011 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 4, 4]
def baseStart_1235011 : Nat := 118140960795 + 1235011 * 2 ^ 59
def prefixEnd_1235011 : Nat := 4983230072969 + 3 ^ 40 * 1235011 * 2
def baseEnd_1235011 : Nat := 422769504393315164988529

theorem tailTrace_1235011 : CollatzResearch.WordTrace tailWord_1235011 prefixEnd_1235011 422769504393315164988529 := by
  unfold tailWord_1235011
  simp only [CollatzResearch.WordTrace]
  refine ⟨45044551728773544931464887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30029701152515696620976591 45044551728773544931464887)
  ·
    refine ⟨67566827593160317397197331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45044551728773544931464887 67566827593160317397197331)
    ·
      refine ⟨101350241389740476095795997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67566827593160317397197331 101350241389740476095795997)
      ·
        refine ⟨38006340521152678535923499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101350241389740476095795997 38006340521152678535923499)
        ·
          refine ⟨57009510781729017803885249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38006340521152678535923499 57009510781729017803885249)
          ·
            refine ⟨42757133086296763352913937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57009510781729017803885249 42757133086296763352913937)
            ·
              refine ⟨32067849814722572514685453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42757133086296763352913937 32067849814722572514685453)
              ·
                refine ⟨12025443680520964693007045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32067849814722572514685453 12025443680520964693007045)
                ·
                  refine ⟨2254770690097680879938821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12025443680520964693007045 2254770690097680879938821)
                  ·
                    refine ⟨422769504393315164988529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2254770690097680879938821 422769504393315164988529)
                    ·
                      rfl

theorem cell22_1235011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 4].length) (baseStart_1235011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235011 prefixEnd_1235011 := by exact prefixLift 1235011
  have htrace : WordTrace (prefixWord ++ tailWord_1235011) baseStart_1235011 baseEnd_1235011 := by
    simpa [prefixWord, tailWord_1235011, baseEnd_1235011] using wordTrace_append hprefix tailTrace_1235011
  have hstable : (prefixWord ++ tailWord_1235011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235011).length < 2 ^ (prefixWord ++ tailWord_1235011).sum := by decide
  have hdescent : baseEnd_1235011 < baseStart_1235011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235045 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_1235045 : Nat := 118140960795 + 1235045 * 2 ^ 59
def prefixEnd_1235045 : Nat := 4983230072969 + 3 ^ 40 * 1235045 * 2
def baseEnd_1235045 : Nat := 422781143288150409638425

theorem tailTrace_1235045 : CollatzResearch.WordTrace tailWord_1235045 prefixEnd_1235045 422781143288150409638425 := by
  unfold tailWord_1235045
  simp only [CollatzResearch.WordTrace]
  refine ⟨45045791810650368738202589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30030527873766912492135059 45045791810650368738202589)
  ·
    refine ⟨16892171928993888276825971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45045791810650368738202589 16892171928993888276825971)
    ·
      refine ⟨25338257893490832415238957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16892171928993888276825971 25338257893490832415238957)
      ·
        refine ⟨9501846710059062155714609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25338257893490832415238957 9501846710059062155714609)
        ·
          refine ⟨7126385032544296616785957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9501846710059062155714609 7126385032544296616785957)
          ·
            refine ⟨1336197193602055615647367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7126385032544296616785957 1336197193602055615647367)
            ·
              refine ⟨2004295790403083423471051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336197193602055615647367 2004295790403083423471051)
              ·
                refine ⟨3006443685604625135206577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004295790403083423471051 3006443685604625135206577)
                ·
                  refine ⟨2254832764203468851404933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006443685604625135206577 2254832764203468851404933)
                  ·
                    refine ⟨422781143288150409638425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2254832764203468851404933 422781143288150409638425)
                    ·
                      rfl

theorem cell22_1235045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_1235045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235045 prefixEnd_1235045 := by exact prefixLift 1235045
  have htrace : WordTrace (prefixWord ++ tailWord_1235045) baseStart_1235045 baseEnd_1235045 := by
    simpa [prefixWord, tailWord_1235045, baseEnd_1235045] using wordTrace_append hprefix tailTrace_1235045
  have hstable : (prefixWord ++ tailWord_1235045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235045).length < 2 ^ (prefixWord ++ tailWord_1235045).sum := by decide
  have hdescent : baseEnd_1235045 < baseStart_1235045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235075 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 3, 3]
def baseStart_1235075 : Nat := 118140960795 + 1235075 * 2 ^ 59
def prefixEnd_1235075 : Nat := 4983230072969 + 3 ^ 40 * 1235075 * 2
def baseEnd_1235075 : Nat := 422791412901240331388333

theorem tailTrace_1235075 : CollatzResearch.WordTrace tailWord_1235075 prefixEnd_1235075 422791412901240331388333 := by
  unfold tailWord_1235075
  simp only [CollatzResearch.WordTrace]
  refine ⟨45046886000541683861794679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30031257333694455907863119 45046886000541683861794679)
  ·
    refine ⟨67570329000812525792692019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45046886000541683861794679 67570329000812525792692019)
    ·
      refine ⟨101355493501218788689038029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67570329000812525792692019 101355493501218788689038029)
      ·
        refine ⟨38008310062957045758389261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101355493501218788689038029 38008310062957045758389261)
        ·
          refine ⟨14253116273608892159395973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38008310062957045758389261 14253116273608892159395973)
          ·
            refine ⟨2672459301301667279886745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14253116273608892159395973 2672459301301667279886745)
            ·
              refine ⟨2004344475976250459915059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672459301301667279886745 2004344475976250459915059)
              ·
                refine ⟨3006516713964375689872589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004344475976250459915059 3006516713964375689872589)
                ·
                  refine ⟨1127443767736640883702221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3006516713964375689872589 1127443767736640883702221)
                  ·
                    refine ⟨422791412901240331388333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1127443767736640883702221 422791412901240331388333)
                    ·
                      rfl

theorem cell22_1235075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 3].length) (baseStart_1235075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235075 prefixEnd_1235075 := by exact prefixLift 1235075
  have htrace : WordTrace (prefixWord ++ tailWord_1235075) baseStart_1235075 baseEnd_1235075 := by
    simpa [prefixWord, tailWord_1235075, baseEnd_1235075] using wordTrace_append hprefix tailTrace_1235075
  have hstable : (prefixWord ++ tailWord_1235075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235075).length < 2 ^ (prefixWord ++ tailWord_1235075).sum := by decide
  have hdescent : baseEnd_1235075 < baseStart_1235075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235163 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 2, 4]
def baseStart_1235163 : Nat := 118140960795 + 1235163 * 2 ^ 59
def prefixEnd_1235163 : Nat := 4983230072969 + 3 ^ 40 * 1235163 * 2
def baseEnd_1235163 : Nat := 422821537099637435188063

theorem tailTrace_1235163 : CollatzResearch.WordTrace tailWord_1235163 prefixEnd_1235163 422821537099637435188063 := by
  unfold tailWord_1235163
  simp only [CollatzResearch.WordTrace]
  refine ⟨45050095624222874890998143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30033397082815249927332095 45050095624222874890998143)
  ·
    refine ⟨67575143436334312336497215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45050095624222874890998143 67575143436334312336497215)
    ·
      refine ⟨101362715154501468504745823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67575143436334312336497215 101362715154501468504745823)
      ·
        refine ⟨152044072731752202757118735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101362715154501468504745823 152044072731752202757118735)
        ·
          refine ⟨228066109097628304135678103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152044072731752202757118735 228066109097628304135678103)
          ·
            refine ⟨342099163646442456203517155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228066109097628304135678103 342099163646442456203517155)
            ·
              refine ⟨513148745469663684305275733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342099163646442456203517155 513148745469663684305275733)
              ·
                refine ⟨3006730930486310650226225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 513148745469663684305275733 3006730930486310650226225)
                ·
                  refine ⟨2255048197864732987669669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006730930486310650226225 2255048197864732987669669)
                  ·
                    refine ⟨422821537099637435188063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2255048197864732987669669 422821537099637435188063)
                    ·
                      rfl

theorem cell22_1235163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 4].length) (baseStart_1235163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235163 prefixEnd_1235163 := by exact prefixLift 1235163
  have htrace : WordTrace (prefixWord ++ tailWord_1235163) baseStart_1235163 baseEnd_1235163 := by
    simpa [prefixWord, tailWord_1235163, baseEnd_1235163] using wordTrace_append hprefix tailTrace_1235163
  have hstable : (prefixWord ++ tailWord_1235163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235163).length < 2 ^ (prefixWord ++ tailWord_1235163).sum := by decide
  have hdescent : baseEnd_1235163 < baseStart_1235163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235165 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1235165 : Nat := 118140960795 + 1235165 * 2 ^ 59
def prefixEnd_1235165 : Nat := 4983230072969 + 3 ^ 40 * 1235165 * 2
def baseEnd_1235165 : Nat := 422822221740510096638057

theorem tailTrace_1235165 : CollatzResearch.WordTrace tailWord_1235165 prefixEnd_1235165 422822221740510096638057 := by
  unfold tailWord_1235165
  simp only [CollatzResearch.WordTrace]
  refine ⟨45050168570215629232570949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30033445713477086155047299 45050168570215629232570949)
  ·
    refine ⟨8446906606915430481107053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45050168570215629232570949 8446906606915430481107053)
    ·
      refine ⟨3167589977593286430415145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8446906606915430481107053 3167589977593286430415145)
      ·
        refine ⟨2375692483194964822811359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3167589977593286430415145 2375692483194964822811359)
        ·
          refine ⟨3563538724792447234217039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2375692483194964822811359 3563538724792447234217039)
          ·
            refine ⟨5345308087188670851325559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563538724792447234217039 5345308087188670851325559)
            ·
              refine ⟨8017962130783006276988339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345308087188670851325559 8017962130783006276988339)
              ·
                refine ⟨12026943196174509415482509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8017962130783006276988339 12026943196174509415482509)
                ·
                  refine ⟨4510103698565441030805941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12026943196174509415482509 4510103698565441030805941)
                  ·
                    refine ⟨422822221740510096638057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4510103698565441030805941 422822221740510096638057)
                    ·
                      rfl

theorem cell22_1235165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1235165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235165 prefixEnd_1235165 := by exact prefixLift 1235165
  have htrace : WordTrace (prefixWord ++ tailWord_1235165) baseStart_1235165 baseEnd_1235165 := by
    simpa [prefixWord, tailWord_1235165, baseEnd_1235165] using wordTrace_append hprefix tailTrace_1235165
  have hstable : (prefixWord ++ tailWord_1235165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235165).length < 2 ^ (prefixWord ++ tailWord_1235165).sum := by decide
  have hdescent : baseEnd_1235165 < baseStart_1235165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235210 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 5, 3]
def baseStart_1235210 : Nat := 118140960795 + 1235210 * 2 ^ 59
def prefixEnd_1235210 : Nat := 4983230072969 + 3 ^ 40 * 1235210 * 2
def baseEnd_1235210 : Nat := 422837626160144979262919

theorem tailTrace_1235210 : CollatzResearch.WordTrace tailWord_1235210 prefixEnd_1235210 422837626160144979262919 := by
  unfold tailWord_1235210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262952463763150479489771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30034539903368401278639389 11262952463763150479489771)
  ·
    refine ⟨16894428695644725719234657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11262952463763150479489771 16894428695644725719234657)
    ·
      refine ⟨12670821521733544289425993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16894428695644725719234657 12670821521733544289425993)
      ·
        refine ⟨9503116141300158217069495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12670821521733544289425993 9503116141300158217069495)
        ·
          refine ⟨14254674211950237325604243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9503116141300158217069495 14254674211950237325604243)
          ·
            refine ⟨21382011317925355988406365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14254674211950237325604243 21382011317925355988406365)
            ·
              refine ⟨8018254244222008495652387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21382011317925355988406365 8018254244222008495652387)
              ·
                refine ⟨12027381366333012743478581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8018254244222008495652387 12027381366333012743478581)
                ·
                  refine ⟨1127567003093719944701117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12027381366333012743478581 1127567003093719944701117)
                  ·
                    refine ⟨422837626160144979262919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1127567003093719944701117 422837626160144979262919)
                    ·
                      rfl

theorem cell22_1235210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_1235210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235210 prefixEnd_1235210 := by exact prefixLift 1235210
  have htrace : WordTrace (prefixWord ++ tailWord_1235210) baseStart_1235210 baseEnd_1235210 := by
    simpa [prefixWord, tailWord_1235210, baseEnd_1235210] using wordTrace_append hprefix tailTrace_1235210
  have hstable : (prefixWord ++ tailWord_1235210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235210).length < 2 ^ (prefixWord ++ tailWord_1235210).sum := by decide
  have hdescent : baseEnd_1235210 < baseStart_1235210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235227 : List Nat := [1, 1, 1, 1, 1, 1, 7, 5, 1, 3]
def baseStart_1235227 : Nat := 118140960795 + 1235227 * 2 ^ 59
def prefixEnd_1235227 : Nat := 4983230072969 + 3 ^ 40 * 1235227 * 2
def baseEnd_1235227 : Nat := 422843445607562601587867

theorem tailTrace_1235227 : CollatzResearch.WordTrace tailWord_1235227 prefixEnd_1235227 422843445607562601587867 := by
  unfold tailWord_1235227
  simp only [CollatzResearch.WordTrace]
  refine ⟨45052429895991013821327935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30034953263994009214218623 45052429895991013821327935)
  ·
    refine ⟨67578644843986520731991903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45052429895991013821327935 67578644843986520731991903)
    ·
      refine ⟨101367967265979781097987855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67578644843986520731991903 101367967265979781097987855)
      ·
        refine ⟨152051950898969671646981783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101367967265979781097987855 152051950898969671646981783)
        ·
          refine ⟨228077926348454507470472675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152051950898969671646981783 228077926348454507470472675)
          ·
            refine ⟨342116889522681761205709013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228077926348454507470472675 342116889522681761205709013)
            ·
              refine ⟨8018364598187853778258805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 342116889522681761205709013 8018364598187853778258805)
              ·
                refine ⟨751721681080111291711763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8018364598187853778258805 751721681080111291711763)
                ·
                  refine ⟨1127582521620166937567645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751721681080111291711763 1127582521620166937567645)
                  ·
                    refine ⟨422843445607562601587867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1127582521620166937567645 422843445607562601587867)
                    ·
                      rfl

theorem cell22_1235227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 3].length) (baseStart_1235227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235227 prefixEnd_1235227 := by exact prefixLift 1235227
  have htrace : WordTrace (prefixWord ++ tailWord_1235227) baseStart_1235227 baseEnd_1235227 := by
    simpa [prefixWord, tailWord_1235227, baseEnd_1235227] using wordTrace_append hprefix tailTrace_1235227
  have hstable : (prefixWord ++ tailWord_1235227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235227).length < 2 ^ (prefixWord ++ tailWord_1235227).sum := by decide
  have hdescent : baseEnd_1235227 < baseStart_1235227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235332 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_1235332 : Nat := 118140960795 + 1235332 * 2 ^ 59
def prefixEnd_1235332 : Nat := 4983230072969 + 3 ^ 40 * 1235332 * 2
def baseEnd_1235332 : Nat := 422879389253377327712545

theorem tailTrace_1235332 : CollatzResearch.WordTrace tailWord_1235332 prefixEnd_1235332 422879389253377327712545 := by
  unfold tailWord_1235332
  simp only [CollatzResearch.WordTrace]
  refine ⟨22528129780305308376950125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30037506373740411169266833 22528129780305308376950125)
  ·
    refine ⟨8448048667614490641356297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22528129780305308376950125 8448048667614490641356297)
    ·
      refine ⟨6336036500710867981017223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8448048667614490641356297 6336036500710867981017223)
      ·
        refine ⟨9504054751066301971525835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6336036500710867981017223 9504054751066301971525835)
        ·
          refine ⟨14256082126599452957288753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9504054751066301971525835 14256082126599452957288753)
          ·
            refine ⟨10692061594949589717966565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14256082126599452957288753 10692061594949589717966565)
            ·
              refine ⟨2004761549053048072118731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10692061594949589717966565 2004761549053048072118731)
              ·
                refine ⟨3007142323579572108178097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004761549053048072118731 3007142323579572108178097)
                ·
                  refine ⟨2255356742684679081133573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3007142323579572108178097 2255356742684679081133573)
                  ·
                    refine ⟨422879389253377327712545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2255356742684679081133573 422879389253377327712545)
                    ·
                      rfl

theorem cell22_1235332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_1235332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235332 prefixEnd_1235332 := by exact prefixLift 1235332
  have htrace : WordTrace (prefixWord ++ tailWord_1235332) baseStart_1235332 baseEnd_1235332 := by
    simpa [prefixWord, tailWord_1235332, baseEnd_1235332] using wordTrace_append hprefix tailTrace_1235332
  have hstable : (prefixWord ++ tailWord_1235332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235332).length < 2 ^ (prefixWord ++ tailWord_1235332).sum := by decide
  have hdescent : baseEnd_1235332 < baseStart_1235332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235360 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 2, 6]
def baseStart_1235360 : Nat := 118140960795 + 1235360 * 2 ^ 59
def prefixEnd_1235360 : Nat := 4983230072969 + 3 ^ 40 * 1235360 * 2
def baseEnd_1235360 : Nat := 422888974225594588012459

theorem tailTrace_1235360 : CollatzResearch.WordTrace tailWord_1235360 prefixEnd_1235360 422888974225594588012459 := by
  unfold tailWord_1235360
  simp only [CollatzResearch.WordTrace]
  refine ⟨22528640402254588767959767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30038187203006118357279689 22528640402254588767959767)
  ·
    refine ⟨33792960603381883151939651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22528640402254588767959767 33792960603381883151939651)
    ·
      refine ⟨50689440905072824727909477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33792960603381883151939651 50689440905072824727909477)
      ·
        refine ⟨9504270169701154636483027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50689440905072824727909477 9504270169701154636483027)
        ·
          refine ⟨14256405254551731954724541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9504270169701154636483027 14256405254551731954724541)
          ·
            refine ⟨5346151970456899483021703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14256405254551731954724541 5346151970456899483021703)
            ·
              refine ⟨8019227955685349224532555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5346151970456899483021703 8019227955685349224532555)
              ·
                refine ⟨12028841933528023836798833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8019227955685349224532555 12028841933528023836798833)
                ·
                  refine ⟨9021631450146017877599125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12028841933528023836798833 9021631450146017877599125)
                  ·
                    refine ⟨422888974225594588012459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9021631450146017877599125 422888974225594588012459)
                    ·
                      rfl

theorem cell22_1235360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_1235360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235360 prefixEnd_1235360 := by exact prefixLift 1235360
  have htrace : WordTrace (prefixWord ++ tailWord_1235360) baseStart_1235360 baseEnd_1235360 := by
    simpa [prefixWord, tailWord_1235360, baseEnd_1235360] using wordTrace_append hprefix tailTrace_1235360
  have hstable : (prefixWord ++ tailWord_1235360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235360).length < 2 ^ (prefixWord ++ tailWord_1235360).sum := by decide
  have hdescent : baseEnd_1235360 < baseStart_1235360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235467 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 4, 4]
def baseStart_1235467 : Nat := 118140960795 + 1235467 * 2 ^ 59
def prefixEnd_1235467 : Nat := 4983230072969 + 3 ^ 40 * 1235467 * 2
def baseEnd_1235467 : Nat := 422925602512281975587131

theorem tailTrace_1235467 : CollatzResearch.WordTrace tailWord_1235467 prefixEnd_1235467 422925602512281975587131 := by
  unfold tailWord_1235467
  simp only [CollatzResearch.WordTrace]
  refine ⟨45061183415121534810064655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30040788943414356540043103 45061183415121534810064655)
  ·
    refine ⟨67591775122682302215096983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45061183415121534810064655 67591775122682302215096983)
    ·
      refine ⟨101387662684023453322645475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67591775122682302215096983 101387662684023453322645475)
      ·
        refine ⟨152081494026035179983968213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101387662684023453322645475 152081494026035179983968213)
        ·
          refine ⟨3564410016235199530874255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 152081494026035179983968213 3564410016235199530874255)
          ·
            refine ⟨5346615024352799296311383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3564410016235199530874255 5346615024352799296311383)
            ·
              refine ⟨8019922536529198944467075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5346615024352799296311383 8019922536529198944467075)
              ·
                refine ⟨12029883804793798416700613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8019922536529198944467075 12029883804793798416700613)
                ·
                  refine ⟨2255603213398837203131365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12029883804793798416700613 2255603213398837203131365)
                  ·
                    refine ⟨422925602512281975587131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2255603213398837203131365 422925602512281975587131)
                    ·
                      rfl

theorem cell22_1235467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 4].length) (baseStart_1235467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235467 prefixEnd_1235467 := by exact prefixLift 1235467
  have htrace : WordTrace (prefixWord ++ tailWord_1235467) baseStart_1235467 baseEnd_1235467 := by
    simpa [prefixWord, tailWord_1235467, baseEnd_1235467] using wordTrace_append hprefix tailTrace_1235467
  have hstable : (prefixWord ++ tailWord_1235467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235467).length < 2 ^ (prefixWord ++ tailWord_1235467).sum := by decide
  have hdescent : baseEnd_1235467 < baseStart_1235467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235550 : List Nat := [4, 4, 1, 2, 1, 1, 3, 6]
def baseStart_1235550 : Nat := 118140960795 + 1235550 * 2 ^ 59
def prefixEnd_1235550 : Nat := 4983230072969 + 3 ^ 40 * 1235550 * 2
def baseEnd_1235550 : Nat := 46994890567610825084653

theorem tailTrace_1235550 : CollatzResearch.WordTrace tailWord_1235550 prefixEnd_1235550 46994890567610825084653 := by
  unfold tailWord_1235550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5633026334227604998167013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30042807115880559990224069 5633026334227604998167013)
  ·
    refine ⟨1056192437667675937156315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5633026334227604998167013 1056192437667675937156315)
    ·
      refine ⟨1584288656501513905734473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056192437667675937156315 1584288656501513905734473)
      ·
        refine ⟨1188216492376135429300855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1584288656501513905734473 1188216492376135429300855)
        ·
          refine ⟨1782324738564203143951283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188216492376135429300855 1782324738564203143951283)
          ·
            refine ⟨2673487107846304715926925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782324738564203143951283 2673487107846304715926925)
            ·
              refine ⟨1002557665442364268472597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2673487107846304715926925 1002557665442364268472597)
              ·
                refine ⟨46994890567610825084653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1002557665442364268472597 46994890567610825084653)
                ·
                  rfl

theorem cell22_1235550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_1235550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235550 prefixEnd_1235550 := by exact prefixLift 1235550
  have htrace : WordTrace (prefixWord ++ tailWord_1235550) baseStart_1235550 baseEnd_1235550 := by
    simpa [prefixWord, tailWord_1235550, baseEnd_1235550] using wordTrace_append hprefix tailTrace_1235550
  have hstable : (prefixWord ++ tailWord_1235550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235550).length < 2 ^ (prefixWord ++ tailWord_1235550).sum := by decide
  have hdescent : baseEnd_1235550 < baseStart_1235550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235587 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 3, 5]
def baseStart_1235587 : Nat := 118140960795 + 1235587 * 2 ^ 59
def prefixEnd_1235587 : Nat := 4983230072969 + 3 ^ 40 * 1235587 * 2
def baseEnd_1235587 : Nat := 422966680964641662586763

theorem tailTrace_1235587 : CollatzResearch.WordTrace tailWord_1235587 prefixEnd_1235587 422966680964641662586763 := by
  unfold tailWord_1235587
  simp only [CollatzResearch.WordTrace]
  refine ⟨45065560174686795304433015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30043706783124530202955343 45065560174686795304433015)
  ·
    refine ⟨67598340262030192956649523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45065560174686795304433015 67598340262030192956649523)
    ·
      refine ⟨101397510393045289434974285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67598340262030192956649523 101397510393045289434974285)
      ·
        refine ⟨38024066397391983538115357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101397510393045289434974285 38024066397391983538115357)
        ·
          refine ⟨14259024899021993826793259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38024066397391983538115357 14259024899021993826793259)
          ·
            refine ⟨21388537348532990740189889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14259024899021993826793259 21388537348532990740189889)
            ·
              refine ⟨16041403011399743055142417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21388537348532990740189889 16041403011399743055142417)
              ·
                refine ⟨12031052258549807291356813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16041403011399743055142417 12031052258549807291356813)
                ·
                  refine ⟨4511644596956177734258805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12031052258549807291356813 4511644596956177734258805)
                  ·
                    refine ⟨422966680964641662586763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4511644596956177734258805 422966680964641662586763)
                    ·
                      rfl

theorem cell22_1235587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_1235587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235587 prefixEnd_1235587 := by exact prefixLift 1235587
  have htrace : WordTrace (prefixWord ++ tailWord_1235587) baseStart_1235587 baseEnd_1235587 := by
    simpa [prefixWord, tailWord_1235587, baseEnd_1235587] using wordTrace_append hprefix tailTrace_1235587
  have hstable : (prefixWord ++ tailWord_1235587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235587).length < 2 ^ (prefixWord ++ tailWord_1235587).sum := by decide
  have hdescent : baseEnd_1235587 < baseStart_1235587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235589 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 6]
def baseStart_1235589 : Nat := 118140960795 + 1235589 * 2 ^ 59
def prefixEnd_1235589 : Nat := 4983230072969 + 3 ^ 40 * 1235589 * 2
def baseEnd_1235589 : Nat := 140989121868504774678919

theorem tailTrace_1235589 : CollatzResearch.WordTrace tailWord_1235589 prefixEnd_1235589 140989121868504774678919 := by
  unfold tailWord_1235589
  simp only [CollatzResearch.WordTrace]
  refine ⟨45065633120679549646005821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30043755413786366430670547 45065633120679549646005821)
  ·
    refine ⟨16899612420254831117252183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45065633120679549646005821 16899612420254831117252183)
    ·
      refine ⟨25349418630382246675878275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16899612420254831117252183 25349418630382246675878275)
      ·
        refine ⟨38024127945573370013817413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25349418630382246675878275 38024127945573370013817413)
        ·
          refine ⟨7129523989795006877590765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38024127945573370013817413 7129523989795006877590765)
          ·
            refine ⟨2673571496173127579096537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7129523989795006877590765 2673571496173127579096537)
            ·
              refine ⟨2005178622129845684322403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2673571496173127579096537 2005178622129845684322403)
              ·
                refine ⟨3007767933194768526483605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005178622129845684322403 3007767933194768526483605)
                ·
                  refine ⟨140989121868504774678919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3007767933194768526483605 140989121868504774678919)
                  ·
                    rfl

theorem cell22_1235589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_1235589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235589 prefixEnd_1235589 := by exact prefixLift 1235589
  have htrace : WordTrace (prefixWord ++ tailWord_1235589) baseStart_1235589 baseEnd_1235589 := by
    simpa [prefixWord, tailWord_1235589, baseEnd_1235589] using wordTrace_append hprefix tailTrace_1235589
  have hstable : (prefixWord ++ tailWord_1235589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235589).length < 2 ^ (prefixWord ++ tailWord_1235589).sum := by decide
  have hdescent : baseEnd_1235589 < baseStart_1235589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235709 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_1235709 : Nat := 118140960795 + 1235709 * 2 ^ 59
def prefixEnd_1235709 : Nat := 4983230072969 + 3 ^ 40 * 1235709 * 2
def baseEnd_1235709 : Nat := 423008444057874011036389

theorem tailTrace_1235709 : CollatzResearch.WordTrace tailWord_1235709 prefixEnd_1235709 423008444057874011036389 := by
  unfold tailWord_1235709
  simp only [CollatzResearch.WordTrace]
  refine ⟨45070009880244810140374181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30046673253496540093582787 45070009880244810140374181)
  ·
    refine ⟨8450626852545901901320159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45070009880244810140374181 8450626852545901901320159)
    ·
      refine ⟨12675940278818852851980239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8450626852545901901320159 12675940278818852851980239)
      ·
        refine ⟨19013910418228279277970359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12675940278818852851980239 19013910418228279277970359)
        ·
          refine ⟨28520865627342418916955539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19013910418228279277970359 28520865627342418916955539)
          ·
            refine ⟨42781298441013628375433309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28520865627342418916955539 42781298441013628375433309)
            ·
              refine ⟨16042986915380110640787491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42781298441013628375433309 16042986915380110640787491)
              ·
                refine ⟨24064480373070165961181237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16042986915380110640787491 24064480373070165961181237)
                ·
                  refine ⟨2256045034975328058860741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24064480373070165961181237 2256045034975328058860741)
                  ·
                    refine ⟨423008444057874011036389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2256045034975328058860741 423008444057874011036389)
                    ·
                      rfl

theorem cell22_1235709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_1235709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235709 prefixEnd_1235709 := by exact prefixLift 1235709
  have htrace : WordTrace (prefixWord ++ tailWord_1235709) baseStart_1235709 baseEnd_1235709 := by
    simpa [prefixWord, tailWord_1235709, baseEnd_1235709] using wordTrace_append hprefix tailTrace_1235709
  have hstable : (prefixWord ++ tailWord_1235709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235709).length < 2 ^ (prefixWord ++ tailWord_1235709).sum := by decide
  have hdescent : baseEnd_1235709 < baseStart_1235709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235726 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_1235726 : Nat := 118140960795 + 1235726 * 2 ^ 59
def prefixEnd_1235726 : Nat := 4983230072969 + 3 ^ 40 * 1235726 * 2
def baseEnd_1235726 : Nat := 423014263505291633361337

theorem tailTrace_1235726 : CollatzResearch.WordTrace tailWord_1235726 prefixEnd_1235726 423014263505291633361337 := by
  unfold tailWord_1235726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5633828740147902755467879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30047086614122148029162021 5633828740147902755467879)
  ·
    refine ⟨8450743110221854133201819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5633828740147902755467879 8450743110221854133201819)
    ·
      refine ⟨12676114665332781199802729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8450743110221854133201819 12676114665332781199802729)
      ·
        refine ⟨9507085998999585899852047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12676114665332781199802729 9507085998999585899852047)
        ·
          refine ⟨14260628998499378849778071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9507085998999585899852047 14260628998499378849778071)
          ·
            refine ⟨21390943497749068274667107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14260628998499378849778071 21390943497749068274667107)
            ·
              refine ⟨32086415246623602412000661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21390943497749068274667107 32086415246623602412000661)
              ·
                refine ⟨1504050714685481363062531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32086415246623602412000661 1504050714685481363062531)
                ·
                  refine ⟨2256076072028222044593797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504050714685481363062531 2256076072028222044593797)
                  ·
                    refine ⟨423014263505291633361337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2256076072028222044593797 423014263505291633361337)
                    ·
                      rfl

theorem cell22_1235726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_1235726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235726 prefixEnd_1235726 := by exact prefixLift 1235726
  have htrace : WordTrace (prefixWord ++ tailWord_1235726) baseStart_1235726 baseEnd_1235726 := by
    simpa [prefixWord, tailWord_1235726, baseEnd_1235726] using wordTrace_append hprefix tailTrace_1235726
  have hstable : (prefixWord ++ tailWord_1235726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235726).length < 2 ^ (prefixWord ++ tailWord_1235726).sum := by decide
  have hdescent : baseEnd_1235726 < baseStart_1235726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235743 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 1, 4]
def baseStart_1235743 : Nat := 118140960795 + 1235743 * 2 ^ 59
def prefixEnd_1235743 : Nat := 4983230072969 + 3 ^ 40 * 1235743 * 2
def baseEnd_1235743 : Nat := 423020082952709255686285

theorem tailTrace_1235743 : CollatzResearch.WordTrace tailWord_1235743 prefixEnd_1235743 423020082952709255686285 := by
  unfold tailWord_1235743
  simp only [CollatzResearch.WordTrace]
  refine ⟨45071249962121633947111883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30047499974747755964741255 45071249962121633947111883)
  ·
    refine ⟨67606874943182450920667825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45071249962121633947111883 67606874943182450920667825)
    ·
      refine ⟨50705156207386838190500869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67606874943182450920667825 50705156207386838190500869)
      ·
        refine ⟨9507216788885032160718913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50705156207386838190500869 9507216788885032160718913)
        ·
          refine ⟨7130412591663774120539185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9507216788885032160718913 7130412591663774120539185)
          ·
            refine ⟨5347809443747830590404389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7130412591663774120539185 5347809443747830590404389)
            ·
              refine ⟨1002714270702718235700823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5347809443747830590404389 1002714270702718235700823)
              ·
                refine ⟨1504071406054077353551235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002714270702718235700823 1504071406054077353551235)
                ·
                  refine ⟨2256107109081116030326853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504071406054077353551235 2256107109081116030326853)
                  ·
                    refine ⟨423020082952709255686285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2256107109081116030326853 423020082952709255686285)
                    ·
                      rfl

theorem cell22_1235743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 4].length) (baseStart_1235743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235743 prefixEnd_1235743 := by exact prefixLift 1235743
  have htrace : WordTrace (prefixWord ++ tailWord_1235743) baseStart_1235743 baseEnd_1235743 := by
    simpa [prefixWord, tailWord_1235743, baseEnd_1235743] using wordTrace_append hprefix tailTrace_1235743
  have hstable : (prefixWord ++ tailWord_1235743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235743).length < 2 ^ (prefixWord ++ tailWord_1235743).sum := by decide
  have hdescent : baseEnd_1235743 < baseStart_1235743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235756 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 4, 3]
def baseStart_1235756 : Nat := 118140960795 + 1235756 * 2 ^ 59
def prefixEnd_1235756 : Nat := 4983230072969 + 3 ^ 40 * 1235756 * 2
def baseEnd_1235756 : Nat := 423024533118381555111245

theorem tailTrace_1235756 : CollatzResearch.WordTrace tailWord_1235756 prefixEnd_1235756 423024533118381555111245 := by
  unfold tailWord_1235756
  simp only [CollatzResearch.WordTrace]
  refine ⟨22535862055537268583667561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30047816074049691444890081 22535862055537268583667561)
  ·
    refine ⟨16901896541652951437750671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22535862055537268583667561 16901896541652951437750671)
    ·
      refine ⟨25352844812479427156626007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16901896541652951437750671 25352844812479427156626007)
      ·
        refine ⟨38029267218719140734939011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25352844812479427156626007 38029267218719140734939011)
        ·
          refine ⟨57043900828078711102408517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38029267218719140734939011 57043900828078711102408517)
          ·
            refine ⟨10695731405264758331701597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57043900828078711102408517 10695731405264758331701597)
            ·
              refine ⟨4010899276974284374388099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10695731405264758331701597 4010899276974284374388099)
              ·
                refine ⟨6016348915461426561582149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010899276974284374388099 6016348915461426561582149)
                ·
                  refine ⟨1128065421649017480296653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6016348915461426561582149 1128065421649017480296653)
                  ·
                    refine ⟨423024533118381555111245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128065421649017480296653 423024533118381555111245)
                    ·
                      rfl

theorem cell22_1235756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_1235756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235756 prefixEnd_1235756 := by exact prefixLift 1235756
  have htrace : WordTrace (prefixWord ++ tailWord_1235756) baseStart_1235756 baseEnd_1235756 := by
    simpa [prefixWord, tailWord_1235756, baseEnd_1235756] using wordTrace_append hprefix tailTrace_1235756
  have hstable : (prefixWord ++ tailWord_1235756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235756).length < 2 ^ (prefixWord ++ tailWord_1235756).sum := by decide
  have hdescent : baseEnd_1235756 < baseStart_1235756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235758 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_1235758 : Nat := 118140960795 + 1235758 * 2 ^ 59
def prefixEnd_1235758 : Nat := 4983230072969 + 3 ^ 40 * 1235758 * 2
def baseEnd_1235758 : Nat := 141008405919751405520413

theorem tailTrace_1235758 : CollatzResearch.WordTrace tailWord_1235758 prefixEnd_1235758 141008405919751405520413 := by
  unfold tailWord_1235758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5633974632133411438613491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30047864704711527672605285 5633974632133411438613491)
  ·
    refine ⟨8450961948200117157920237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5633974632133411438613491 8450961948200117157920237)
    ·
      refine ⟨3169110730575043934220089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8450961948200117157920237 3169110730575043934220089)
      ·
        refine ⟨2376833047931282950665067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3169110730575043934220089 2376833047931282950665067)
        ·
          refine ⟨3565249571896924425997601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2376833047931282950665067 3565249571896924425997601)
          ·
            refine ⟨2673937178922693319498201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3565249571896924425997601 2673937178922693319498201)
            ·
              refine ⟨2005452884192019989623651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2673937178922693319498201 2005452884192019989623651)
              ·
                refine ⟨3008179326288029984435477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005452884192019989623651 3008179326288029984435477)
                ·
                  refine ⟨141008405919751405520413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3008179326288029984435477 141008405919751405520413)
                  ·
                    rfl

theorem cell22_1235758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_1235758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235758 prefixEnd_1235758 := by exact prefixLift 1235758
  have htrace : WordTrace (prefixWord ++ tailWord_1235758) baseStart_1235758 baseEnd_1235758 := by
    simpa [prefixWord, tailWord_1235758, baseEnd_1235758] using wordTrace_append hprefix tailTrace_1235758
  have hstable : (prefixWord ++ tailWord_1235758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235758).length < 2 ^ (prefixWord ++ tailWord_1235758).sum := by decide
  have hdescent : baseEnd_1235758 < baseStart_1235758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235784 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 2, 7]
def baseStart_1235784 : Nat := 118140960795 + 1235784 * 2 ^ 59
def prefixEnd_1235784 : Nat := 4983230072969 + 3 ^ 40 * 1235784 * 2
def baseEnd_1235784 : Nat := 423034118090598815411159

theorem tailTrace_1235784 : CollatzResearch.WordTrace tailWord_1235784 prefixEnd_1235784 423034118090598815411159 := by
  unfold tailWord_1235784
  simp only [CollatzResearch.WordTrace]
  refine ⟨22536372677486548974677203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30048496903315398632902937 22536372677486548974677203)
  ·
    refine ⟨33804559016229823462015805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22536372677486548974677203 33804559016229823462015805)
    ·
      refine ⟨12676709631086183798255927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33804559016229823462015805 12676709631086183798255927)
      ·
        refine ⟨19015064446629275697383891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12676709631086183798255927 19015064446629275697383891)
        ·
          refine ⟨28522596669943913546075837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19015064446629275697383891 28522596669943913546075837)
          ·
            refine ⟨10695973751228967579778439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28522596669943913546075837 10695973751228967579778439)
            ·
              refine ⟨16043960626843451369667659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10695973751228967579778439 16043960626843451369667659)
              ·
                refine ⟨24065940940265177054501489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16043960626843451369667659 24065940940265177054501489)
                ·
                  refine ⟨18049455705198882790876117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24065940940265177054501489 18049455705198882790876117)
                  ·
                    refine ⟨423034118090598815411159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18049455705198882790876117 423034118090598815411159)
                    ·
                      rfl

theorem cell22_1235784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_1235784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235784 prefixEnd_1235784 := by exact prefixLift 1235784
  have htrace : WordTrace (prefixWord ++ tailWord_1235784) baseStart_1235784 baseEnd_1235784 := by
    simpa [prefixWord, tailWord_1235784, baseEnd_1235784] using wordTrace_append hprefix tailTrace_1235784
  have hstable : (prefixWord ++ tailWord_1235784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235784).length < 2 ^ (prefixWord ++ tailWord_1235784).sum := by decide
  have hdescent : baseEnd_1235784 < baseStart_1235784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235859 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 10]
def baseStart_1235859 : Nat := 118140960795 + 1235859 * 2 ^ 59
def prefixEnd_1235859 : Nat := 4983230072969 + 3 ^ 40 * 1235859 * 2
def baseEnd_1235859 : Nat := 141019930707774539928643

theorem tailTrace_1235859 : CollatzResearch.WordTrace tailWord_1235859 prefixEnd_1235859 141019930707774539928643 := by
  unfold tailWord_1235859
  simp only [CollatzResearch.WordTrace]
  refine ⟨45075480829701385758334631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30050320553134257172223087 45075480829701385758334631)
  ·
    refine ⟨67613221244552078637501947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45075480829701385758334631 67613221244552078637501947)
    ·
      refine ⟨101419831866828117956252921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67613221244552078637501947 101419831866828117956252921)
      ·
        refine ⟨76064873900121088467189691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101419831866828117956252921 76064873900121088467189691)
        ·
          refine ⟨114097310850181632700784537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76064873900121088467189691 114097310850181632700784537)
          ·
            refine ⟨85572983137636224525588403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114097310850181632700784537 85572983137636224525588403)
            ·
              refine ⟨128359474706454336788382605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85572983137636224525588403 128359474706454336788382605)
              ·
                refine ⟨48134803014920376295643477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128359474706454336788382605 48134803014920376295643477)
                ·
                  refine ⟨141019930707774539928643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 48134803014920376295643477 141019930707774539928643)
                  ·
                    rfl

theorem cell22_1235859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 10].length) (baseStart_1235859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235859 prefixEnd_1235859 := by exact prefixLift 1235859
  have htrace : WordTrace (prefixWord ++ tailWord_1235859) baseStart_1235859 baseEnd_1235859 := by
    simpa [prefixWord, tailWord_1235859, baseEnd_1235859] using wordTrace_append hprefix tailTrace_1235859
  have hstable : (prefixWord ++ tailWord_1235859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235859).length < 2 ^ (prefixWord ++ tailWord_1235859).sum := by decide
  have hdescent : baseEnd_1235859 < baseStart_1235859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235876 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 6]
def baseStart_1235876 : Nat := 118140960795 + 1235876 * 2 ^ 59
def prefixEnd_1235876 : Nat := 4983230072969 + 3 ^ 40 * 1235876 * 2
def baseEnd_1235876 : Nat := 141021870523580414036959

theorem tailTrace_1235876 : CollatzResearch.WordTrace tailWord_1235876 prefixEnd_1235876 141021870523580414036959 := by
  unfold tailWord_1235876
  simp only [CollatzResearch.WordTrace]
  refine ⟨22538050435319898830851741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30050733913759865107802321 22538050435319898830851741)
  ·
    refine ⟨8451768913244962061569403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22538050435319898830851741 8451768913244962061569403)
    ·
      refine ⟨12677653369867443092354105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8451768913244962061569403 12677653369867443092354105)
      ·
        refine ⟨9508240027400582319265579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12677653369867443092354105 9508240027400582319265579)
        ·
          refine ⟨14262360041100873478898369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9508240027400582319265579 14262360041100873478898369)
          ·
            refine ⟨10696770030825655109173777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14262360041100873478898369 10696770030825655109173777)
            ·
              refine ⟨8022577523119241331880333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10696770030825655109173777 8022577523119241331880333)
              ·
                refine ⟨3008466571169715499455125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8022577523119241331880333 3008466571169715499455125)
                ·
                  refine ⟨141021870523580414036959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3008466571169715499455125 141021870523580414036959)
                  ·
                    rfl

theorem cell22_1235876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_1235876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235876 prefixEnd_1235876 := by exact prefixLift 1235876
  have htrace : WordTrace (prefixWord ++ tailWord_1235876) baseStart_1235876 baseEnd_1235876 := by
    simpa [prefixWord, tailWord_1235876, baseEnd_1235876] using wordTrace_append hprefix tailTrace_1235876
  have hstable : (prefixWord ++ tailWord_1235876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235876).length < 2 ^ (prefixWord ++ tailWord_1235876).sum := by decide
  have hdescent : baseEnd_1235876 < baseStart_1235876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235912 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 1, 4]
def baseStart_1235912 : Nat := 118140960795 + 1235912 * 2 ^ 59
def prefixEnd_1235912 : Nat := 4983230072969 + 3 ^ 40 * 1235912 * 2
def baseEnd_1235912 : Nat := 423077935106449148210767

theorem tailTrace_1235912 : CollatzResearch.WordTrace tailWord_1235912 prefixEnd_1235912 423077935106449148210767 := by
  unfold tailWord_1235912
  simp only [CollatzResearch.WordTrace]
  refine ⟨22538706949254687905006995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30051609265672917206675993 22538706949254687905006995)
  ·
    refine ⟨33808060423882031857510493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22538706949254687905006995 33808060423882031857510493)
    ·
      refine ⟨12678022658955761946566435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33808060423882031857510493 12678022658955761946566435)
      ·
        refine ⟨19017033988433642919849653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12678022658955761946566435 19017033988433642919849653)
        ·
          refine ⟨1782846936415654023735905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19017033988433642919849653 1782846936415654023735905)
          ·
            refine ⟨1337135202311740517801929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1782846936415654023735905 1337135202311740517801929)
            ·
              refine ⟨1002851401733805388351447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337135202311740517801929 1002851401733805388351447)
              ·
                refine ⟨1504277102600708082527171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002851401733805388351447 1504277102600708082527171)
                ·
                  refine ⟨2256415653901062123790757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504277102600708082527171 2256415653901062123790757)
                  ·
                    refine ⟨423077935106449148210767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2256415653901062123790757 423077935106449148210767)
                    ·
                      rfl

theorem cell22_1235912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_1235912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235912 prefixEnd_1235912 := by exact prefixLift 1235912
  have htrace : WordTrace (prefixWord ++ tailWord_1235912) baseStart_1235912 baseEnd_1235912 := by
    simpa [prefixWord, tailWord_1235912, baseEnd_1235912] using wordTrace_append hprefix tailTrace_1235912
  have hstable : (prefixWord ++ tailWord_1235912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235912).length < 2 ^ (prefixWord ++ tailWord_1235912).sum := by decide
  have hdescent : baseEnd_1235912 < baseStart_1235912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1235925 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_1235925 : Nat := 118140960795 + 1235925 * 2 ^ 59
def prefixEnd_1235925 : Nat := 4983230072969 + 3 ^ 40 * 1235925 * 2
def baseEnd_1235925 : Nat := 423082385272121447635727

theorem tailTrace_1235925 : CollatzResearch.WordTrace tailWord_1235925 prefixEnd_1235925 423082385272121447635727 := by
  unfold tailWord_1235925
  simp only [CollatzResearch.WordTrace]
  refine ⟨45077888047462279030237229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30051925364974852686824819 45077888047462279030237229)
  ·
    refine ⟨16904208017798354636338961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45077888047462279030237229 16904208017798354636338961)
    ·
      refine ⟨12678156013348765977254221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16904208017798354636338961 12678156013348765977254221)
      ·
        refine ⟨4754308505005787241470333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12678156013348765977254221 4754308505005787241470333)
        ·
          refine ⟨1782865689377170215551375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4754308505005787241470333 1782865689377170215551375)
          ·
            refine ⟨2674298534065755323327063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782865689377170215551375 2674298534065755323327063)
            ·
              refine ⟨4011447801098632984990595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674298534065755323327063 4011447801098632984990595)
              ·
                refine ⟨6017171701647949477485893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011447801098632984990595 6017171701647949477485893)
                ·
                  refine ⟨1128219694058990527028605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6017171701647949477485893 1128219694058990527028605)
                  ·
                    refine ⟨423082385272121447635727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128219694058990527028605 423082385272121447635727)
                    ·
                      rfl

theorem cell22_1235925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_1235925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1235925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1235925 prefixEnd_1235925 := by exact prefixLift 1235925
  have htrace : WordTrace (prefixWord ++ tailWord_1235925) baseStart_1235925 baseEnd_1235925 := by
    simpa [prefixWord, tailWord_1235925, baseEnd_1235925] using wordTrace_append hprefix tailTrace_1235925
  have hstable : (prefixWord ++ tailWord_1235925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1235925).length < 2 ^ (prefixWord ++ tailWord_1235925).sum := by decide
  have hdescent : baseEnd_1235925 < baseStart_1235925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1235925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236011 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 8]
def baseStart_1236011 : Nat := 118140960795 + 1236011 * 2 ^ 59
def prefixEnd_1236011 : Nat := 4983230072969 + 3 ^ 40 * 1236011 * 2
def baseEnd_1236011 : Nat := 141037274943215296661821

theorem tailTrace_1236011 : CollatzResearch.WordTrace tailWord_1236011 prefixEnd_1236011 141037274943215296661821 := by
  unfold tailWord_1236011
  simp only [CollatzResearch.WordTrace]
  refine ⟨45081024725150715717867887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30054016483433810478578591 45081024725150715717867887)
  ·
    refine ⟨67621537087726073576801831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45081024725150715717867887 67621537087726073576801831)
    ·
      refine ⟨101432305631589110365202747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67621537087726073576801831 101432305631589110365202747)
      ·
        refine ⟨152148458447383665547804121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101432305631589110365202747 152148458447383665547804121)
        ·
          refine ⟨114111343835537749160853091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152148458447383665547804121 114111343835537749160853091)
          ·
            refine ⟨171167015753306623741279637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114111343835537749160853091 171167015753306623741279637)
            ·
              refine ⟨8023453863436247987872483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 171167015753306623741279637 8023453863436247987872483)
              ·
                refine ⟨12035180795154371981808725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8023453863436247987872483 12035180795154371981808725)
                ·
                  refine ⟨141037274943215296661821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12035180795154371981808725 141037274943215296661821)
                  ·
                    rfl

theorem cell22_1236011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 8].length) (baseStart_1236011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236011 prefixEnd_1236011 := by exact prefixLift 1236011
  have htrace : WordTrace (prefixWord ++ tailWord_1236011) baseStart_1236011 baseEnd_1236011 := by
    simpa [prefixWord, tailWord_1236011, baseEnd_1236011] using wordTrace_append hprefix tailTrace_1236011
  have hstable : (prefixWord ++ tailWord_1236011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236011).length < 2 ^ (prefixWord ++ tailWord_1236011).sum := by decide
  have hdescent : baseEnd_1236011 < baseStart_1236011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236038 : List Nat := [6, 1, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1236038 : Nat := 118140960795 + 1236038 * 2 ^ 59
def prefixEnd_1236038 : Nat := 4983230072969 + 3 ^ 40 * 1236038 * 2
def baseEnd_1236038 : Nat := 423121067481426819560381

theorem tailTrace_1236038 : CollatzResearch.WordTrace tailWord_1236038 prefixEnd_1236038 423121067481426819560381 := by
  unfold tailWord_1236038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408812796751653104034399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30054672997368599552733845 1408812796751653104034399)
  ·
    refine ⟨2113219195127479656051599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408812796751653104034399 2113219195127479656051599)
    ·
      refine ⟨3169828792691219484077399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2113219195127479656051599 3169828792691219484077399)
      ·
        refine ⟨4754743189036829226116099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169828792691219484077399 4754743189036829226116099)
        ·
          refine ⟨7132114783555243839174149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754743189036829226116099 7132114783555243839174149)
          ·
            refine ⟨1337271521916608219845153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7132114783555243839174149 1337271521916608219845153)
            ·
              refine ⟨1002953641437456164883865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337271521916608219845153 1002953641437456164883865)
              ·
                refine ⟨752215231078092123662899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002953641437456164883865 752215231078092123662899)
                ·
                  refine ⟨1128322846617138185494349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752215231078092123662899 1128322846617138185494349)
                  ·
                    refine ⟨423121067481426819560381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128322846617138185494349 423121067481426819560381)
                    ·
                      rfl

theorem cell22_1236038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1236038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236038 prefixEnd_1236038 := by exact prefixLift 1236038
  have htrace : WordTrace (prefixWord ++ tailWord_1236038) baseStart_1236038 baseEnd_1236038 := by
    simpa [prefixWord, tailWord_1236038, baseEnd_1236038] using wordTrace_append hprefix tailTrace_1236038
  have hstable : (prefixWord ++ tailWord_1236038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236038).length < 2 ^ (prefixWord ++ tailWord_1236038).sum := by decide
  have hdescent : baseEnd_1236038 < baseStart_1236038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236060 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1236060 : Nat := 118140960795 + 1236060 * 2 ^ 59
def prefixEnd_1236060 : Nat := 4983230072969 + 3 ^ 40 * 1236060 * 2
def baseEnd_1236060 : Nat := 423128598531026095510313

theorem tailTrace_1236060 : CollatzResearch.WordTrace tailWord_1236060 prefixEnd_1236060 423128598531026095510313 := by
  unfold tailWord_1236060
  simp only [CollatzResearch.WordTrace]
  refine ⟨22541405950986598543200817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30055207934648798057601089 22541405950986598543200817)
  ·
    refine ⟨16906054463239948907400613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22541405950986598543200817 16906054463239948907400613)
    ·
      refine ⟨3169885211857490420137615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16906054463239948907400613 3169885211857490420137615)
      ·
        refine ⟨4754827817786235630206423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169885211857490420137615 4754827817786235630206423)
        ·
          refine ⟨7132241726679353445309635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754827817786235630206423 7132241726679353445309635)
          ·
            refine ⟨10698362590019030167964453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7132241726679353445309635 10698362590019030167964453)
            ·
              refine ⟨2005942985628568156493335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10698362590019030167964453 2005942985628568156493335)
              ·
                refine ⟨3008914478442852234740003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005942985628568156493335 3008914478442852234740003)
                ·
                  refine ⟨4513371717664278352110005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008914478442852234740003 4513371717664278352110005)
                  ·
                    refine ⟨423128598531026095510313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4513371717664278352110005 423128598531026095510313)
                    ·
                      rfl

theorem cell22_1236060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1236060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236060 prefixEnd_1236060 := by exact prefixLift 1236060
  have htrace : WordTrace (prefixWord ++ tailWord_1236060) baseStart_1236060 baseEnd_1236060 := by
    simpa [prefixWord, tailWord_1236060, baseEnd_1236060] using wordTrace_append hprefix tailTrace_1236060
  have hstable : (prefixWord ++ tailWord_1236060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236060).length < 2 ^ (prefixWord ++ tailWord_1236060).sum := by decide
  have hdescent : baseEnd_1236060 < baseStart_1236060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236062 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1236062 : Nat := 118140960795 + 1236062 * 2 ^ 59
def prefixEnd_1236062 : Nat := 4983230072969 + 3 ^ 40 * 1236062 * 2
def baseEnd_1236062 : Nat := 141043094390632918986769

theorem tailTrace_1236062 : CollatzResearch.WordTrace tailWord_1236062 prefixEnd_1236062 141043094390632918986769 := by
  unfold tailWord_1236062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635360605995743928496805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30055256565310634285316293 5635360605995743928496805)
  ·
    refine ⟨1056630113624201986593151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5635360605995743928496805 1056630113624201986593151)
    ·
      refine ⟨1584945170436302979889727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056630113624201986593151 1584945170436302979889727)
      ·
        refine ⟨2377417755654454469834591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1584945170436302979889727 2377417755654454469834591)
        ·
          refine ⟨3566126633481681704751887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377417755654454469834591 3566126633481681704751887)
          ·
            refine ⟨5349189950222522557127831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566126633481681704751887 5349189950222522557127831)
            ·
              refine ⟨8023784925333783835691747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349189950222522557127831 8023784925333783835691747)
              ·
                refine ⟨12035677388000675753537621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8023784925333783835691747 12035677388000675753537621)
                ·
                  refine ⟨141043094390632918986769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12035677388000675753537621 141043094390632918986769)
                  ·
                    rfl

theorem cell22_1236062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1236062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236062 prefixEnd_1236062 := by exact prefixLift 1236062
  have htrace : WordTrace (prefixWord ++ tailWord_1236062) baseStart_1236062 baseEnd_1236062 := by
    simpa [prefixWord, tailWord_1236062, baseEnd_1236062] using wordTrace_append hprefix tailTrace_1236062
  have hstable : (prefixWord ++ tailWord_1236062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236062).length < 2 ^ (prefixWord ++ tailWord_1236062).sum := by decide
  have hdescent : baseEnd_1236062 < baseStart_1236062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236105 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 3, 3]
def baseStart_1236105 : Nat := 118140960795 + 1236105 * 2 ^ 59
def prefixEnd_1236105 : Nat := 4983230072969 + 3 ^ 40 * 1236105 * 2
def baseEnd_1236105 : Nat := 423144002950660978135175

theorem tailTrace_1236105 : CollatzResearch.WordTrace tailWord_1236105 prefixEnd_1236105 423144002950660978135175 := by
  unfold tailWord_1236105
  simp only [CollatzResearch.WordTrace]
  refine ⟨45084453186810169771789769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30056302124540113181193179 45084453186810169771789769)
  ·
    refine ⟨33813339890107627328842327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45084453186810169771789769 33813339890107627328842327)
    ·
      refine ⟨50720009835161440993263491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33813339890107627328842327 50720009835161440993263491)
      ·
        refine ⟨76080014752742161489895237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50720009835161440993263491 76080014752742161489895237)
        ·
          refine ⟨14265002766139155279355357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76080014752742161489895237 14265002766139155279355357)
          ·
            refine ⟨5349376037302183229758259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14265002766139155279355357 5349376037302183229758259)
            ·
              refine ⟨8024064055953274844637389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349376037302183229758259 8024064055953274844637389)
              ·
                refine ⟨3009024020982478066739021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8024064055953274844637389 3009024020982478066739021)
                ·
                  refine ⟨1128384007868429275027133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3009024020982478066739021 1128384007868429275027133)
                  ·
                    refine ⟨423144002950660978135175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128384007868429275027133 423144002950660978135175)
                    ·
                      rfl

theorem cell22_1236105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_1236105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236105 prefixEnd_1236105 := by exact prefixLift 1236105
  have htrace : WordTrace (prefixWord ++ tailWord_1236105) baseStart_1236105 baseEnd_1236105 := by
    simpa [prefixWord, tailWord_1236105, baseEnd_1236105] using wordTrace_append hprefix tailTrace_1236105
  have hstable : (prefixWord ++ tailWord_1236105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236105).length < 2 ^ (prefixWord ++ tailWord_1236105).sum := by decide
  have hdescent : baseEnd_1236105 < baseStart_1236105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236122 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 3, 3]
def baseStart_1236122 : Nat := 118140960795 + 1236122 * 2 ^ 59
def prefixEnd_1236122 : Nat := 4983230072969 + 3 ^ 40 * 1236122 * 2
def baseEnd_1236122 : Nat := 423149822398078600460123

theorem tailTrace_1236122 : CollatzResearch.WordTrace tailWord_1236122 prefixEnd_1236122 423149822398078600460123 := by
  unfold tailWord_1236122
  simp only [CollatzResearch.WordTrace]
  refine ⟨11271268306937145418789655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30056715485165721116772413 11271268306937145418789655)
  ·
    refine ⟨16906902460405718128184483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11271268306937145418789655 16906902460405718128184483)
    ·
      refine ⟨25360353690608577192276725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16906902460405718128184483 25360353690608577192276725)
      ·
        refine ⟨2377533158494554111775943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25360353690608577192276725 2377533158494554111775943)
        ·
          refine ⟨3566299737741831167663915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377533158494554111775943 3566299737741831167663915)
          ·
            refine ⟨5349449606612746751495873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566299737741831167663915 5349449606612746751495873)
            ·
              refine ⟨4012087204959560063621905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5349449606612746751495873 4012087204959560063621905)
              ·
                refine ⟨3009065403719670047716429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4012087204959560063621905 3009065403719670047716429)
                ·
                  refine ⟨1128399526394876267893661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3009065403719670047716429 1128399526394876267893661)
                  ·
                    refine ⟨423149822398078600460123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128399526394876267893661 423149822398078600460123)
                    ·
                      rfl

theorem cell22_1236122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_1236122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236122 prefixEnd_1236122 := by exact prefixLift 1236122
  have htrace : WordTrace (prefixWord ++ tailWord_1236122) baseStart_1236122 baseEnd_1236122 := by
    simpa [prefixWord, tailWord_1236122, baseEnd_1236122] using wordTrace_append hprefix tailTrace_1236122
  have hstable : (prefixWord ++ tailWord_1236122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236122).length < 2 ^ (prefixWord ++ tailWord_1236122).sum := by decide
  have hdescent : baseEnd_1236122 < baseStart_1236122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236135 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 7]
def baseStart_1236135 : Nat := 118140960795 + 1236135 * 2 ^ 59
def prefixEnd_1236135 : Nat := 4983230072969 + 3 ^ 40 * 1236135 * 2
def baseEnd_1236135 : Nat := 141051424187916966628361

theorem tailTrace_1236135 : CollatzResearch.WordTrace tailWord_1236135 prefixEnd_1236135 141051424187916966628361 := by
  unfold tailWord_1236135
  simp only [CollatzResearch.WordTrace]
  refine ⟨45085547376701484895381859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30057031584467656596921239 45085547376701484895381859)
  ·
    refine ⟨67628321065052227343072789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45085547376701484895381859 67628321065052227343072789)
    ·
      refine ⟨3170077549924323156706537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67628321065052227343072789 3170077549924323156706537)
      ·
        refine ⟨2377558162443242367529903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3170077549924323156706537 2377558162443242367529903)
        ·
          refine ⟨3566337243664863551294855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377558162443242367529903 3566337243664863551294855)
          ·
            refine ⟨5349505865497295326942283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566337243664863551294855 5349505865497295326942283)
            ·
              refine ⟨8024258798245942990413425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349505865497295326942283 8024258798245942990413425)
              ·
                refine ⟨6018194098684457242810069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8024258798245942990413425 6018194098684457242810069)
                ·
                  refine ⟨141051424187916966628361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6018194098684457242810069 141051424187916966628361)
                  ·
                    rfl

theorem cell22_1236135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 7].length) (baseStart_1236135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236135 prefixEnd_1236135 := by exact prefixLift 1236135
  have htrace : WordTrace (prefixWord ++ tailWord_1236135) baseStart_1236135 baseEnd_1236135 := by
    simpa [prefixWord, tailWord_1236135, baseEnd_1236135] using wordTrace_append hprefix tailTrace_1236135
  have hstable : (prefixWord ++ tailWord_1236135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236135).length < 2 ^ (prefixWord ++ tailWord_1236135).sum := by decide
  have hdescent : baseEnd_1236135 < baseStart_1236135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236156 : List Nat := [2, 2, 2, 3, 2, 2, 3, 2, 1, 3]
def baseStart_1236156 : Nat := 118140960795 + 1236156 * 2 ^ 59
def prefixEnd_1236156 : Nat := 4983230072969 + 3 ^ 40 * 1236156 * 2
def baseEnd_1236156 : Nat := 423161461292913845110019

theorem tailTrace_1236156 : CollatzResearch.WordTrace tailWord_1236156 prefixEnd_1236156 423161461292913845110019 := by
  unfold tailWord_1236156
  simp only [CollatzResearch.WordTrace]
  refine ⟨22543156654812702740948161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30057542206416936987930881 22543156654812702740948161)
  ·
    refine ⟨16907367491109527055711121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22543156654812702740948161 16907367491109527055711121)
    ·
      refine ⟨12680525618332145291783341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16907367491109527055711121 12680525618332145291783341)
      ·
        refine ⟨4755197106874554484418753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12680525618332145291783341 4755197106874554484418753)
        ·
          refine ⟨3566397830155915863314065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4755197106874554484418753 3566397830155915863314065)
          ·
            refine ⟨2674798372616936897485549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3566397830155915863314065 2674798372616936897485549)
            ·
              refine ⟨1003049389731351336557081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2674798372616936897485549 1003049389731351336557081)
              ·
                refine ⟨752287042298513502417811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003049389731351336557081 752287042298513502417811)
                ·
                  refine ⟨1128430563447770253626717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752287042298513502417811 1128430563447770253626717)
                  ·
                    refine ⟨423161461292913845110019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128430563447770253626717 423161461292913845110019)
                    ·
                      rfl

theorem cell22_1236156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_1236156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236156 prefixEnd_1236156 := by exact prefixLift 1236156
  have htrace : WordTrace (prefixWord ++ tailWord_1236156) baseStart_1236156 baseEnd_1236156 := by
    simpa [prefixWord, tailWord_1236156, baseEnd_1236156] using wordTrace_append hprefix tailTrace_1236156
  have hstable : (prefixWord ++ tailWord_1236156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236156).length < 2 ^ (prefixWord ++ tailWord_1236156).sum := by decide
  have hdescent : baseEnd_1236156 < baseStart_1236156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236163 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 6]
def baseStart_1236163 : Nat := 118140960795 + 1236163 * 2 ^ 59
def prefixEnd_1236163 : Nat := 4983230072969 + 3 ^ 40 * 1236163 * 2
def baseEnd_1236163 : Nat := 141054619178656053394999

theorem tailTrace_1236163 : CollatzResearch.WordTrace tailWord_1236163 prefixEnd_1236163 141054619178656053394999 := by
  unfold tailWord_1236163
  simp only [CollatzResearch.WordTrace]
  refine ⟨45086568620600045677401143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30057712413733363784934095 45086568620600045677401143)
  ·
    refine ⟨67629852930900068516101715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45086568620600045677401143 67629852930900068516101715)
    ·
      refine ⟨101444779396350102774152573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67629852930900068516101715 101444779396350102774152573)
      ·
        refine ⟨38041792273631288540307215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101444779396350102774152573 38041792273631288540307215)
        ·
          refine ⟨57062688410446932810460823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38041792273631288540307215 57062688410446932810460823)
          ·
            refine ⟨85594032615670399215691235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57062688410446932810460823 85594032615670399215691235)
            ·
              refine ⟨128391048923505598823536853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85594032615670399215691235 128391048923505598823536853)
              ·
                refine ⟨3009165209144662472426645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 128391048923505598823536853 3009165209144662472426645)
                ·
                  refine ⟨141054619178656053394999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3009165209144662472426645 141054619178656053394999)
                  ·
                    rfl

theorem cell22_1236163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 6].length) (baseStart_1236163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236163 prefixEnd_1236163 := by exact prefixLift 1236163
  have htrace : WordTrace (prefixWord ++ tailWord_1236163) baseStart_1236163 baseEnd_1236163 := by
    simpa [prefixWord, tailWord_1236163, baseEnd_1236163] using wordTrace_append hprefix tailTrace_1236163
  have hstable : (prefixWord ++ tailWord_1236163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236163).length < 2 ^ (prefixWord ++ tailWord_1236163).sum := by decide
  have hdescent : baseEnd_1236163 < baseStart_1236163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236225 : List Nat := [1, 2, 4, 1, 1, 3, 3, 7]
def baseStart_1236225 : Nat := 118140960795 + 1236225 * 2 ^ 59
def prefixEnd_1236225 : Nat := 4983230072969 + 3 ^ 40 * 1236225 * 2
def baseEnd_1236225 : Nat := 47020564600335629459423

theorem tailTrace_1236225 : CollatzResearch.WordTrace tailWord_1236225 prefixEnd_1236225 47020564600335629459423 := by
  unfold tailWord_1236225
  simp only [CollatzResearch.WordTrace]
  refine ⟨45088829946375430266158129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30059219964250286844105419 45088829946375430266158129)
  ·
    refine ⟨33816622459781572699618597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45088829946375430266158129 33816622459781572699618597)
    ·
      refine ⟨6340616711209044881178487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33816622459781572699618597 6340616711209044881178487)
      ·
        refine ⟨9510925066813567321767731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6340616711209044881178487 9510925066813567321767731)
        ·
          refine ⟨14266387600220350982651597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9510925066813567321767731 14266387600220350982651597)
          ·
            refine ⟨5349895350082631618494349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14266387600220350982651597 5349895350082631618494349)
            ·
              refine ⟨2006210756280986856935381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5349895350082631618494349 2006210756280986856935381)
              ·
                refine ⟨47020564600335629459423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2006210756280986856935381 47020564600335629459423)
                ·
                  rfl

theorem cell22_1236225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 7].length) (baseStart_1236225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236225 prefixEnd_1236225 := by exact prefixLift 1236225
  have htrace : WordTrace (prefixWord ++ tailWord_1236225) baseStart_1236225 baseEnd_1236225 := by
    simpa [prefixWord, tailWord_1236225, baseEnd_1236225] using wordTrace_append hprefix tailTrace_1236225
  have hstable : (prefixWord ++ tailWord_1236225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236225).length < 2 ^ (prefixWord ++ tailWord_1236225).sum := by decide
  have hdescent : baseEnd_1236225 < baseStart_1236225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236274 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_1236274 : Nat := 118140960795 + 1236274 * 2 ^ 59
def prefixEnd_1236274 : Nat := 4983230072969 + 3 ^ 40 * 1236274 * 2
def baseEnd_1236274 : Nat := 423201855104400870659657

theorem tailTrace_1236274 : CollatzResearch.WordTrace tailWord_1236274 prefixEnd_1236274 423201855104400870659657 := by
  unfold tailWord_1236274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11272654280799477908672969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30060411415465274423127917 11272654280799477908672969)
  ·
    refine ⟨8454490710599608431504727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11272654280799477908672969 8454490710599608431504727)
    ·
      refine ⟨12681736065899412647257091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8454490710599608431504727 12681736065899412647257091)
      ·
        refine ⟨19022604098849118970885637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12681736065899412647257091 19022604098849118970885637)
        ·
          refine ⟨3566738268534209807041057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19022604098849118970885637 3566738268534209807041057)
          ·
            refine ⟨2675053701400657355280793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3566738268534209807041057 2675053701400657355280793)
            ·
              refine ⟨2006290276050493016460595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675053701400657355280793 2006290276050493016460595)
              ·
                refine ⟨3009435414075739524690893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006290276050493016460595 3009435414075739524690893)
                ·
                  refine ⟨1128538280278402321759085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3009435414075739524690893 1128538280278402321759085)
                  ·
                    refine ⟨423201855104400870659657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128538280278402321759085 423201855104400870659657)
                    ·
                      rfl

theorem cell22_1236274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_1236274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236274 prefixEnd_1236274 := by exact prefixLift 1236274
  have htrace : WordTrace (prefixWord ++ tailWord_1236274) baseStart_1236274 baseEnd_1236274 := by
    simpa [prefixWord, tailWord_1236274, baseEnd_1236274] using wordTrace_append hprefix tailTrace_1236274
  have hstable : (prefixWord ++ tailWord_1236274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236274).length < 2 ^ (prefixWord ++ tailWord_1236274).sum := by decide
  have hdescent : baseEnd_1236274 < baseStart_1236274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236332 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 6]
def baseStart_1236332 : Nat := 118140960795 + 1236332 * 2 ^ 59
def prefixEnd_1236332 : Nat := 4983230072969 + 3 ^ 40 * 1236332 * 2
def baseEnd_1236332 : Nat := 141073903229902684236493

theorem tailTrace_1236332 : CollatzResearch.WordTrace tailWord_1236332 prefixEnd_1236332 141073903229902684236493 := by
  unfold tailWord_1236332
  simp only [CollatzResearch.WordTrace]
  refine ⟨22546366278493893770151625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30061821704658525026868833 22546366278493893770151625)
  ·
    refine ⟨16909774708870420327613719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22546366278493893770151625 16909774708870420327613719)
    ·
      refine ⟨25364662063305630491420579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16909774708870420327613719 25364662063305630491420579)
      ·
        refine ⟨38046993094958445737130869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25364662063305630491420579 38046993094958445737130869)
        ·
          refine ⟨3566905602652354287856019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38046993094958445737130869 3566905602652354287856019)
          ·
            refine ⟨5350358403978531431784029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3566905602652354287856019 5350358403978531431784029)
            ·
              refine ⟨2006384401491949286919011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5350358403978531431784029 2006384401491949286919011)
              ·
                refine ⟨3009576602237923930378517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006384401491949286919011 3009576602237923930378517)
                ·
                  refine ⟨141073903229902684236493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3009576602237923930378517 141073903229902684236493)
                  ·
                    rfl

theorem cell22_1236332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_1236332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236332 prefixEnd_1236332 := by exact prefixLift 1236332
  have htrace : WordTrace (prefixWord ++ tailWord_1236332) baseStart_1236332 baseEnd_1236332 := by
    simpa [prefixWord, tailWord_1236332, baseEnd_1236332] using wordTrace_append hprefix tailTrace_1236332
  have hstable : (prefixWord ++ tailWord_1236332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236332).length < 2 ^ (prefixWord ++ tailWord_1236332).sum := by decide
  have hdescent : baseEnd_1236332 < baseStart_1236332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236345 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_1236345 : Nat := 118140960795 + 1236345 * 2 ^ 59
def prefixEnd_1236345 : Nat := 4983230072969 + 3 ^ 40 * 1236345 * 2
def baseEnd_1236345 : Nat := 423226159855380352134439

theorem tailTrace_1236345 : CollatzResearch.WordTrace tailWord_1236345 prefixEnd_1236345 423226159855380352134439 := by
  unfold tailWord_1236345
  simp only [CollatzResearch.WordTrace]
  refine ⟨45093206705940690760526489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30062137803960460507017659 45093206705940690760526489)
  ·
    refine ⟨33819905029455518070394867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45093206705940690760526489 33819905029455518070394867)
    ·
      refine ⟨50729857544183277105592301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33819905029455518070394867 50729857544183277105592301)
      ·
        refine ⟨19023696579068728914597113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50729857544183277105592301 19023696579068728914597113)
        ·
          refine ⟨14267772434301546685947835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19023696579068728914597113 14267772434301546685947835)
          ·
            refine ⟨21401658651452320028921753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14267772434301546685947835 21401658651452320028921753)
            ·
              refine ⟨16051243988589240021691315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21401658651452320028921753 16051243988589240021691315)
              ·
                refine ⟨24076865982883860032536973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16051243988589240021691315 24076865982883860032536973)
                ·
                  refine ⟨9028824743581447512201365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24076865982883860032536973 9028824743581447512201365)
                  ·
                    refine ⟨423226159855380352134439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9028824743581447512201365 423226159855380352134439)
                    ·
                      rfl

theorem cell22_1236345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_1236345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236345 prefixEnd_1236345 := by exact prefixLift 1236345
  have htrace : WordTrace (prefixWord ++ tailWord_1236345) baseStart_1236345 baseEnd_1236345 := by
    simpa [prefixWord, tailWord_1236345, baseEnd_1236345] using wordTrace_append hprefix tailTrace_1236345
  have hstable : (prefixWord ++ tailWord_1236345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236345).length < 2 ^ (prefixWord ++ tailWord_1236345).sum := by decide
  have hdescent : baseEnd_1236345 < baseStart_1236345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236381 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1236381 : Nat := 118140960795 + 1236381 * 2 ^ 59
def prefixEnd_1236381 : Nat := 4983230072969 + 3 ^ 40 * 1236381 * 2
def baseEnd_1236381 : Nat := 423238483391088258234329

theorem tailTrace_1236381 : CollatzResearch.WordTrace tailWord_1236381 prefixEnd_1236381 423238483391088258234329 := by
  unfold tailWord_1236381
  simp only [CollatzResearch.WordTrace]
  refine ⟨45094519733810268908836997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30063013155873512605891331 45094519733810268908836997)
  ·
    refine ⟨8455222450089425420406937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45094519733810268908836997 8455222450089425420406937)
    ·
      refine ⟨6341416837567069065305203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8455222450089425420406937 6341416837567069065305203)
      ·
        refine ⟨9512125256350603597957805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6341416837567069065305203 9512125256350603597957805)
        ·
          refine ⟨3567046971131476349234177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9512125256350603597957805 3567046971131476349234177)
          ·
            refine ⟨2675285228348607261925633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3567046971131476349234177 2675285228348607261925633)
            ·
              refine ⟨2006463921261455446444225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675285228348607261925633 2006463921261455446444225)
              ·
                refine ⟨1504847940946091584833169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006463921261455446444225 1504847940946091584833169)
                ·
                  refine ⟨1128635955709568688624877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504847940946091584833169 1128635955709568688624877)
                  ·
                    refine ⟨423238483391088258234329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128635955709568688624877 423238483391088258234329)
                    ·
                      rfl

theorem cell22_1236381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1236381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236381 prefixEnd_1236381 := by exact prefixLift 1236381
  have htrace : WordTrace (prefixWord ++ tailWord_1236381) baseStart_1236381 baseEnd_1236381 := by
    simpa [prefixWord, tailWord_1236381, baseEnd_1236381] using wordTrace_append hprefix tailTrace_1236381
  have hstable : (prefixWord ++ tailWord_1236381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236381).length < 2 ^ (prefixWord ++ tailWord_1236381).sum := by decide
  have hdescent : baseEnd_1236381 < baseStart_1236381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236426 : List Nat := [3, 1, 2, 1, 2, 3, 1, 5, 1, 3]
def baseStart_1236426 : Nat := 118140960795 + 1236426 * 2 ^ 59
def prefixEnd_1236426 : Nat := 4983230072969 + 3 ^ 40 * 1236426 * 2
def baseEnd_1236426 : Nat := 423253887810723140859191

theorem tailTrace_1236426 : CollatzResearch.WordTrace tailWord_1236426 prefixEnd_1236426 423253887810723140859191 := by
  unfold tailWord_1236426
  simp only [CollatzResearch.WordTrace]
  refine ⟨11274040254661810398556283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30064107345764827729483421 11274040254661810398556283)
  ·
    refine ⟨16911060381992715597834425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11274040254661810398556283 16911060381992715597834425)
    ·
      refine ⟨12683295286494536698375819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16911060381992715597834425 12683295286494536698375819)
      ·
        refine ⟨19024942929741805047563729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12683295286494536698375819 19024942929741805047563729)
        ·
          refine ⟨14268707197306353785672797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19024942929741805047563729 14268707197306353785672797)
          ·
            refine ⟨5350765198989882669627299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14268707197306353785672797 5350765198989882669627299)
            ·
              refine ⟨8026147798484824004440949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5350765198989882669627299 8026147798484824004440949)
              ·
                refine ⟨752451356107952250416339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8026147798484824004440949 752451356107952250416339)
                ·
                  refine ⟨1128677034161928375624509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752451356107952250416339 1128677034161928375624509)
                  ·
                    refine ⟨423253887810723140859191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128677034161928375624509 423253887810723140859191)
                    ·
                      rfl

theorem cell22_1236426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_1236426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236426 prefixEnd_1236426 := by exact prefixLift 1236426
  have htrace : WordTrace (prefixWord ++ tailWord_1236426) baseStart_1236426 baseEnd_1236426 := by
    simpa [prefixWord, tailWord_1236426, baseEnd_1236426] using wordTrace_append hprefix tailTrace_1236426
  have hstable : (prefixWord ++ tailWord_1236426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236426).length < 2 ^ (prefixWord ++ tailWord_1236426).sum := by decide
  have hdescent : baseEnd_1236426 < baseStart_1236426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236437 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1236437 : Nat := 118140960795 + 1236437 * 2 ^ 59
def prefixEnd_1236437 : Nat := 4983230072969 + 3 ^ 40 * 1236437 * 2
def baseEnd_1236437 : Nat := 423257653335522778834157

theorem tailTrace_1236437 : CollatzResearch.WordTrace tailWord_1236437 prefixEnd_1236437 423257653335522778834157 := by
  unfold tailWord_1236437
  simp only [CollatzResearch.WordTrace]
  refine ⟨45096562221607390472875565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30064374814404926981917043 45096562221607390472875565)
  ·
    refine ⟨16911210833102771427328337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45096562221607390472875565 16911210833102771427328337)
    ·
      refine ⟨12683408124827078570496253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16911210833102771427328337 12683408124827078570496253)
      ·
        refine ⟨4756278046810154463936095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12683408124827078570496253 4756278046810154463936095)
        ·
          refine ⟨7134417070215231695904143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4756278046810154463936095 7134417070215231695904143)
          ·
            refine ⟨10701625605322847543856215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7134417070215231695904143 10701625605322847543856215)
            ·
              refine ⟨16052438407984271315784323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10701625605322847543856215 16052438407984271315784323)
              ·
                refine ⟨24078657611976406973676485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16052438407984271315784323 24078657611976406973676485)
                ·
                  refine ⟨4514748302245576307564341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24078657611976406973676485 4514748302245576307564341)
                  ·
                    refine ⟨423257653335522778834157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4514748302245576307564341 423257653335522778834157)
                    ·
                      rfl

theorem cell22_1236437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1236437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236437 prefixEnd_1236437 := by exact prefixLift 1236437
  have htrace : WordTrace (prefixWord ++ tailWord_1236437) baseStart_1236437 baseEnd_1236437 := by
    simpa [prefixWord, tailWord_1236437, baseEnd_1236437] using wordTrace_append hprefix tailTrace_1236437
  have hstable : (prefixWord ++ tailWord_1236437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236437).length < 2 ^ (prefixWord ++ tailWord_1236437).sum := by decide
  have hdescent : baseEnd_1236437 < baseStart_1236437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236452 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1236452 : Nat := 118140960795 + 1236452 * 2 ^ 59
def prefixEnd_1236452 : Nat := 4983230072969 + 3 ^ 40 * 1236452 * 2
def baseEnd_1236452 : Nat := 423262788142067739709111

theorem tailTrace_1236452 : CollatzResearch.WordTrace tailWord_1236452 prefixEnd_1236452 423262788142067739709111 := by
  unfold tailWord_1236452
  simp only [CollatzResearch.WordTrace]
  refine ⟨22548554658276524017335805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30064739544368698689781073 22548554658276524017335805)
  ·
    refine ⟨8455707996853696506500927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22548554658276524017335805 8455707996853696506500927)
    ·
      refine ⟨12683561995280544759751391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8455707996853696506500927 12683561995280544759751391)
      ·
        refine ⟨19025342992920817139627087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12683561995280544759751391 19025342992920817139627087)
        ·
          refine ⟨28538014489381225709440631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19025342992920817139627087 28538014489381225709440631)
          ·
            refine ⟨42807021734071838564160947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28538014489381225709440631 42807021734071838564160947)
            ·
              refine ⟨64210532601107757846241421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42807021734071838564160947 64210532601107757846241421)
              ·
                refine ⟨24078949725415409192340533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64210532601107757846241421 24078949725415409192340533)
                ·
                  refine ⟨2257401536757694611781925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24078949725415409192340533 2257401536757694611781925)
                  ·
                    refine ⟨423262788142067739709111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257401536757694611781925 423262788142067739709111)
                    ·
                      rfl

theorem cell22_1236452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1236452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236452 prefixEnd_1236452 := by exact prefixLift 1236452
  have htrace : WordTrace (prefixWord ++ tailWord_1236452) baseStart_1236452 baseEnd_1236452 := by
    simpa [prefixWord, tailWord_1236452, baseEnd_1236452] using wordTrace_append hprefix tailTrace_1236452
  have hstable : (prefixWord ++ tailWord_1236452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236452).length < 2 ^ (prefixWord ++ tailWord_1236452).sum := by decide
  have hdescent : baseEnd_1236452 < baseStart_1236452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236499 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 4, 3]
def baseStart_1236499 : Nat := 118140960795 + 1236499 * 2 ^ 59
def prefixEnd_1236499 : Nat := 4983230072969 + 3 ^ 40 * 1236499 * 2
def baseEnd_1236499 : Nat := 423278877202575283783967

theorem tailTrace_1236499 : CollatzResearch.WordTrace tailWord_1236499 prefixEnd_1236499 423278877202575283783967 := by
  unfold tailWord_1236499
  simp only [CollatzResearch.WordTrace]
  refine ⟨45098823547382775061632551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30065882364921850041088367 45098823547382775061632551)
  ·
    refine ⟨67648235321074162592448827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45098823547382775061632551 67648235321074162592448827)
    ·
      refine ⟨101472352981611243888673241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67648235321074162592448827 101472352981611243888673241)
      ·
        refine ⟨76104264736208432916504931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101472352981611243888673241 76104264736208432916504931)
        ·
          refine ⟨114156397104312649374757397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76104264736208432916504931 114156397104312649374757397)
          ·
            refine ⟨5351081114264655439441753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114156397104312649374757397 5351081114264655439441753)
            ·
              refine ⟨4013310835698491579581315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5351081114264655439441753 4013310835698491579581315)
              ·
                refine ⟨6019966253547737369371973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4013310835698491579581315 6019966253547737369371973)
                ·
                  refine ⟨1128743672540200756757245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6019966253547737369371973 1128743672540200756757245)
                  ·
                    refine ⟨423278877202575283783967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128743672540200756757245 423278877202575283783967)
                    ·
                      rfl

theorem cell22_1236499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 3].length) (baseStart_1236499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236499 prefixEnd_1236499 := by exact prefixLift 1236499
  have htrace : WordTrace (prefixWord ++ tailWord_1236499) baseStart_1236499 baseEnd_1236499 := by
    simpa [prefixWord, tailWord_1236499, baseEnd_1236499] using wordTrace_append hprefix tailTrace_1236499
  have hstable : (prefixWord ++ tailWord_1236499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236499).length < 2 ^ (prefixWord ++ tailWord_1236499).sum := by decide
  have hdescent : baseEnd_1236499 < baseStart_1236499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236520 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 1, 4]
def baseStart_1236520 : Nat := 118140960795 + 1236520 * 2 ^ 59
def prefixEnd_1236520 : Nat := 4983230072969 + 3 ^ 40 * 1236520 * 2
def baseEnd_1236520 : Nat := 423286065931738229008903

theorem tailTrace_1236520 : CollatzResearch.WordTrace tailWord_1236520 prefixEnd_1236520 423286065931738229008903 := by
  unfold tailWord_1236520
  simp only [CollatzResearch.WordTrace]
  refine ⟨22549794740153347824073507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30066392986871130432098009 22549794740153347824073507)
  ·
    refine ⟨33824692110230021736110261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22549794740153347824073507 33824692110230021736110261)
    ·
      refine ⟨3171064885334064537760337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33824692110230021736110261 3171064885334064537760337)
      ·
        refine ⟨2378298664000548403320253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3171064885334064537760337 2378298664000548403320253)
        ·
          refine ⟨891861999000205651245095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2378298664000548403320253 891861999000205651245095)
          ·
            refine ⟨1337792998500308476867643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891861999000205651245095 1337792998500308476867643)
            ·
              refine ⟨2006689497750462715301465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337792998500308476867643 2006689497750462715301465)
              ·
                refine ⟨1505017123312847036476099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006689497750462715301465 1505017123312847036476099)
                ·
                  refine ⟨2257525684969270554714149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505017123312847036476099 2257525684969270554714149)
                  ·
                    refine ⟨423286065931738229008903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257525684969270554714149 423286065931738229008903)
                    ·
                      rfl

theorem cell22_1236520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_1236520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236520 prefixEnd_1236520 := by exact prefixLift 1236520
  have htrace : WordTrace (prefixWord ++ tailWord_1236520) baseStart_1236520 baseEnd_1236520 := by
    simpa [prefixWord, tailWord_1236520, baseEnd_1236520] using wordTrace_append hprefix tailTrace_1236520
  have hstable : (prefixWord ++ tailWord_1236520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236520).length < 2 ^ (prefixWord ++ tailWord_1236520).sum := by decide
  have hdescent : baseEnd_1236520 < baseStart_1236520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236619 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 6]
def baseStart_1236619 : Nat := 118140960795 + 1236619 * 2 ^ 59
def prefixEnd_1236619 : Nat := 4983230072969 + 3 ^ 40 * 1236619 * 2
def baseEnd_1236619 : Nat := 141106651884978323594533

theorem tailTrace_1236619 : CollatzResearch.WordTrace tailWord_1236619 prefixEnd_1236619 141106651884978323594533 := by
  unfold tailWord_1236619
  simp only [CollatzResearch.WordTrace]
  refine ⟨45103200306948035556000911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30068800204632023704000607 45103200306948035556000911)
  ·
    refine ⟨67654800460422053334001367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45103200306948035556000911 67654800460422053334001367)
    ·
      refine ⟨101482200690633080001002051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67654800460422053334001367 101482200690633080001002051)
      ·
        refine ⟨152223301035949620001503077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101482200690633080001002051 152223301035949620001503077)
        ·
          refine ⟨28541868944240553750281827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152223301035949620001503077 28541868944240553750281827)
          ·
            refine ⟨42812803416360830625422741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28541868944240553750281827 42812803416360830625422741)
            ·
              refine ⟨2006850160141913935566691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42812803416360830625422741 2006850160141913935566691)
              ·
                refine ⟨3010275240212870903350037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006850160141913935566691 3010275240212870903350037)
                ·
                  refine ⟨141106651884978323594533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3010275240212870903350037 141106651884978323594533)
                  ·
                    rfl

theorem cell22_1236619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 6].length) (baseStart_1236619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236619 prefixEnd_1236619 := by exact prefixLift 1236619
  have htrace : WordTrace (prefixWord ++ tailWord_1236619) baseStart_1236619 baseEnd_1236619 := by
    simpa [prefixWord, tailWord_1236619, baseEnd_1236619] using wordTrace_append hprefix tailTrace_1236619
  have hstable : (prefixWord ++ tailWord_1236619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236619).length < 2 ^ (prefixWord ++ tailWord_1236619).sum := by decide
  have hdescent : baseEnd_1236619 < baseStart_1236619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236638 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1236638 : Nat := 118140960795 + 1236638 * 2 ^ 59
def prefixEnd_1236638 : Nat := 4983230072969 + 3 ^ 40 * 1236638 * 2
def baseEnd_1236638 : Nat := 423326459743225254558541

theorem tailTrace_1236638 : CollatzResearch.WordTrace tailWord_1236638 prefixEnd_1236638 423326459743225254558541 := by
  unfold tailWord_1236638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5637986661734900225117821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30069262195919467867295045 5637986661734900225117821)
  ·
    refine ⟨2114244998150587584419183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5637986661734900225117821 2114244998150587584419183)
    ·
      refine ⟨3171367497225881376628775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2114244998150587584419183 3171367497225881376628775)
      ·
        refine ⟨4757051245838822064943163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3171367497225881376628775 4757051245838822064943163)
        ·
          refine ⟨7135576868758233097414745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4757051245838822064943163 7135576868758233097414745)
          ·
            refine ⟨5351682651568674823061059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7135576868758233097414745 5351682651568674823061059)
            ·
              refine ⟨8027523977353012234591589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5351682651568674823061059 8027523977353012234591589)
              ·
                refine ⟨1505160745753689793985923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8027523977353012234591589 1505160745753689793985923)
                ·
                  refine ⟨2257741118630534690978885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505160745753689793985923 2257741118630534690978885)
                  ·
                    refine ⟨423326459743225254558541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257741118630534690978885 423326459743225254558541)
                    ·
                      rfl

theorem cell22_1236638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1236638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236638 prefixEnd_1236638 := by exact prefixLift 1236638
  have htrace : WordTrace (prefixWord ++ tailWord_1236638) baseStart_1236638 baseEnd_1236638 := by
    simpa [prefixWord, tailWord_1236638, baseEnd_1236638] using wordTrace_append hprefix tailTrace_1236638
  have hstable : (prefixWord ++ tailWord_1236638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236638).length < 2 ^ (prefixWord ++ tailWord_1236638).sum := by decide
  have hdescent : baseEnd_1236638 < baseStart_1236638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236666 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_1236666 : Nat := 118140960795 + 1236666 * 2 ^ 59
def prefixEnd_1236666 : Nat := 4983230072969 + 3 ^ 40 * 1236666 * 2
def baseEnd_1236666 : Nat := 423336044715442514858455

theorem tailTrace_1236666 : CollatzResearch.WordTrace tailWord_1236666 prefixEnd_1236666 423336044715442514858455 := by
  unfold tailWord_1236666
  simp only [CollatzResearch.WordTrace]
  refine ⟨11276228634444440645740463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30069943025185175055307901 11276228634444440645740463)
  ·
    refine ⟨16914342951666660968610695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11276228634444440645740463 16914342951666660968610695)
    ·
      refine ⟨25371514427499991452916043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16914342951666660968610695 25371514427499991452916043)
      ·
        refine ⟨38057271641249987179374065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25371514427499991452916043 38057271641249987179374065)
        ·
          refine ⟨28542953730937490384530549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38057271641249987179374065 28542953730937490384530549)
          ·
            refine ⟨2675901912275389723549739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28542953730937490384530549 2675901912275389723549739)
            ·
              refine ⟨4013852868413084585324609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2675901912275389723549739 4013852868413084585324609)
              ·
                refine ⟨3010389651309813438993457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4013852868413084585324609 3010389651309813438993457)
                ·
                  refine ⟨2257792238482360079245093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3010389651309813438993457 2257792238482360079245093)
                  ·
                    refine ⟨423336044715442514858455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257792238482360079245093 423336044715442514858455)
                    ·
                      rfl

theorem cell22_1236666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_1236666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236666 prefixEnd_1236666 := by exact prefixLift 1236666
  have htrace : WordTrace (prefixWord ++ tailWord_1236666) baseStart_1236666 baseEnd_1236666 := by
    simpa [prefixWord, tailWord_1236666, baseEnd_1236666] using wordTrace_append hprefix tailTrace_1236666
  have hstable : (prefixWord ++ tailWord_1236666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236666).length < 2 ^ (prefixWord ++ tailWord_1236666).sum := by decide
  have hdescent : baseEnd_1236666 < baseStart_1236666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236670 : List Nat := [4, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_1236670 : Nat := 118140960795 + 1236670 * 2 ^ 59
def prefixEnd_1236670 : Nat := 4983230072969 + 3 ^ 40 * 1236670 * 2
def baseEnd_1236670 : Nat := 141112471332395945919481

theorem tailTrace_1236670 : CollatzResearch.WordTrace tailWord_1236670 prefixEnd_1236670 141112471332395945919481 := by
  unfold tailWord_1236670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638132553720408908263433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30070040286508847510738309 5638132553720408908263433)
  ·
    refine ⟨4228599415290306681197575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5638132553720408908263433 4228599415290306681197575)
    ·
      refine ⟨6342899122935460021796363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4228599415290306681197575 6342899122935460021796363)
      ·
        refine ⟨9514348684403190032694545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6342899122935460021796363 9514348684403190032694545)
        ·
          refine ⟨7135761513302392524520909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9514348684403190032694545 7135761513302392524520909)
          ·
            refine ⟨2675910567488397196695341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7135761513302392524520909 2675910567488397196695341)
            ·
              refine ⟨1003466462808148948760753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2675910567488397196695341 1003466462808148948760753)
              ·
                refine ⟨752599847106111711570565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003466462808148948760753 752599847106111711570565)
                ·
                  refine ⟨141112471332395945919481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752599847106111711570565 141112471332395945919481)
                  ·
                    rfl

theorem cell22_1236670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_1236670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236670 prefixEnd_1236670 := by exact prefixLift 1236670
  have htrace : WordTrace (prefixWord ++ tailWord_1236670) baseStart_1236670 baseEnd_1236670 := by
    simpa [prefixWord, tailWord_1236670, baseEnd_1236670] using wordTrace_append hprefix tailTrace_1236670
  have hstable : (prefixWord ++ tailWord_1236670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236670).length < 2 ^ (prefixWord ++ tailWord_1236670).sum := by decide
  have hdescent : baseEnd_1236670 < baseStart_1236670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236696 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 5, 3]
def baseStart_1236696 : Nat := 118140960795 + 1236696 * 2 ^ 59
def prefixEnd_1236696 : Nat := 4983230072969 + 3 ^ 40 * 1236696 * 2
def baseEnd_1236696 : Nat := 423346314328532436608363

theorem tailTrace_1236696 : CollatzResearch.WordTrace tailWord_1236696 prefixEnd_1236696 423346314328532436608363 := by
  unfold tailWord_1236696
  simp only [CollatzResearch.WordTrace]
  refine ⟨22553004363834538853276971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30070672485112718471035961 22553004363834538853276971)
  ·
    refine ⟨33829506545751808279915457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22553004363834538853276971 33829506545751808279915457)
    ·
      refine ⟨25372129909313856209936593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33829506545751808279915457 25372129909313856209936593)
      ·
        refine ⟨19029097431985392157452445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25372129909313856209936593 19029097431985392157452445)
        ·
          refine ⟨7135911536994522059044667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19029097431985392157452445 7135911536994522059044667)
          ·
            refine ⟨10703867305491783088567001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7135911536994522059044667 10703867305491783088567001)
            ·
              refine ⟨8027900479118837316425251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10703867305491783088567001 8027900479118837316425251)
              ·
                refine ⟨12041850718678255974637877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8027900479118837316425251 12041850718678255974637877)
                ·
                  refine ⟨1128923504876086497622301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12041850718678255974637877 1128923504876086497622301)
                  ·
                    refine ⟨423346314328532436608363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128923504876086497622301 423346314328532436608363)
                    ·
                      rfl

theorem cell22_1236696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_1236696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236696 prefixEnd_1236696 := by exact prefixLift 1236696
  have htrace : WordTrace (prefixWord ++ tailWord_1236696) baseStart_1236696 baseEnd_1236696 := by
    simpa [prefixWord, tailWord_1236696, baseEnd_1236696] using wordTrace_append hprefix tailTrace_1236696
  have hstable : (prefixWord ++ tailWord_1236696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236696).length < 2 ^ (prefixWord ++ tailWord_1236696).sum := by decide
  have hdescent : baseEnd_1236696 < baseStart_1236696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236700 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1236700 : Nat := 118140960795 + 1236700 * 2 ^ 59
def prefixEnd_1236700 : Nat := 4983230072969 + 3 ^ 40 * 1236700 * 2
def baseEnd_1236700 : Nat := 423347683610277759508351

theorem tailTrace_1236700 : CollatzResearch.WordTrace tailWord_1236700 prefixEnd_1236700 423347683610277759508351 := by
  unfold tailWord_1236700
  simp only [CollatzResearch.WordTrace]
  refine ⟨22553077309827293194849777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30070769746436390926466369 22553077309827293194849777)
  ·
    refine ⟨16914807982370469896137333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22553077309827293194849777 16914807982370469896137333)
    ·
      refine ⟨1585763248347231552762875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16914807982370469896137333 1585763248347231552762875)
      ·
        refine ⟨2378644872520847329144313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585763248347231552762875 2378644872520847329144313)
        ·
          refine ⟨1783983654390635496858235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2378644872520847329144313 1783983654390635496858235)
          ·
            refine ⟨2675975481585953245287353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783983654390635496858235 2675975481585953245287353)
            ·
              refine ⟨2006981611189464933965515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675975481585953245287353 2006981611189464933965515)
              ·
                refine ⟨3010472416784197400948273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006981611189464933965515 3010472416784197400948273)
                ·
                  refine ⟨2257854312588148050711205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3010472416784197400948273 2257854312588148050711205)
                  ·
                    refine ⟨423347683610277759508351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2257854312588148050711205 423347683610277759508351)
                    ·
                      rfl

theorem cell22_1236700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1236700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236700 prefixEnd_1236700 := by exact prefixLift 1236700
  have htrace : WordTrace (prefixWord ++ tailWord_1236700) baseStart_1236700 baseEnd_1236700 := by
    simpa [prefixWord, tailWord_1236700, baseEnd_1236700] using wordTrace_append hprefix tailTrace_1236700
  have hstable : (prefixWord ++ tailWord_1236700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236700).length < 2 ^ (prefixWord ++ tailWord_1236700).sum := by decide
  have hdescent : baseEnd_1236700 < baseStart_1236700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1236713 : List Nat := [1, 2, 1, 1, 1, 2, 3, 7, 1, 3]
def baseStart_1236713 : Nat := 118140960795 + 1236713 * 2 ^ 59
def prefixEnd_1236713 : Nat := 4983230072969 + 3 ^ 40 * 1236713 * 2
def baseEnd_1236713 : Nat := 423352133775950058933311

theorem tailTrace_1236713 : CollatzResearch.WordTrace tailWord_1236713 prefixEnd_1236713 423352133775950058933311 := by
  unfold tailWord_1236713
  simp only [CollatzResearch.WordTrace]
  refine ⟨45106628768607489609922793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30071085845738326406615195 45106628768607489609922793)
  ·
    refine ⟨33829971576455617207442095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45106628768607489609922793 33829971576455617207442095)
    ·
      refine ⟨50744957364683425811163143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33829971576455617207442095 50744957364683425811163143)
      ·
        refine ⟨76117436047025138716744715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50744957364683425811163143 76117436047025138716744715)
        ·
          refine ⟨114176154070537708075117073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76117436047025138716744715 114176154070537708075117073)
          ·
            refine ⟨85632115552903281056337805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114176154070537708075117073 85632115552903281056337805)
            ·
              refine ⟨32112043332338730396126677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85632115552903281056337805 32112043332338730396126677)
              ·
                refine ⟨752626015601688993659219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32112043332338730396126677 752626015601688993659219)
                ·
                  refine ⟨1128939023402533490488829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752626015601688993659219 1128939023402533490488829)
                  ·
                    refine ⟨423352133775950058933311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128939023402533490488829 423352133775950058933311)
                    ·
                      rfl

theorem cell22_1236713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 3].length) (baseStart_1236713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1236713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1236713 prefixEnd_1236713 := by exact prefixLift 1236713
  have htrace : WordTrace (prefixWord ++ tailWord_1236713) baseStart_1236713 baseEnd_1236713 := by
    simpa [prefixWord, tailWord_1236713, baseEnd_1236713] using wordTrace_append hprefix tailTrace_1236713
  have hstable : (prefixWord ++ tailWord_1236713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1236713).length < 2 ^ (prefixWord ++ tailWord_1236713).sum := by decide
  have hdescent : baseEnd_1236713 < baseStart_1236713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1236713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
