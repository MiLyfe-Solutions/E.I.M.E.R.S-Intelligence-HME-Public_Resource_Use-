import V185TrunkScan23Chunk1140

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6758495 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 3]
def baseStart_6758495 : Nat := 118140960795 + 6758495 * 2 ^ 59
def prefixEnd_6758495 : Nat := 4983230072969 + 3 ^ 40 * 6758495 * 2
def baseEnd_6758495 : Nat := 3470356436008640090930753

theorem tailTrace_6758495 : CollatzResearch.WordTrace tailWord_6758495 prefixEnd_6758495 3470356436008640090930753 := by
  unfold tailWord_6758495
  simp only [CollatzResearch.WordTrace]
  refine ⟨246502563650134348895852939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164335042433422899263901959 246502563650134348895852939)
  ·
    refine ⟨369753845475201523343779409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246502563650134348895852939 369753845475201523343779409)
    ·
      refine ⟨277315384106401142507834557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369753845475201523343779409 277315384106401142507834557)
      ·
        refine ⟨103993269039900428440437959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277315384106401142507834557 103993269039900428440437959)
        ·
          refine ⟨155989903559850642660656939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103993269039900428440437959 155989903559850642660656939)
          ·
            refine ⟨233984855339775963990985409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155989903559850642660656939 233984855339775963990985409)
            ·
              refine ⟨175488641504831972993239057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233984855339775963990985409 175488641504831972993239057)
              ·
                refine ⟨131616481128623979744929293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175488641504831972993239057 131616481128623979744929293)
                ·
                  refine ⟨49356180423233992404348485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131616481128623979744929293 49356180423233992404348485)
                  ·
                    refine ⟨9254283829356373575815341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49356180423233992404348485 9254283829356373575815341)
                    ·
                      refine ⟨3470356436008640090930753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9254283829356373575815341 3470356436008640090930753)
                      ·
                        rfl

theorem cell23_6758495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_6758495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758495 prefixEnd_6758495 := by exact prefixLift 6758495
  have htrace : WordTrace (prefixWord ++ tailWord_6758495) baseStart_6758495 baseEnd_6758495 := by
    simpa [prefixWord, tailWord_6758495, baseEnd_6758495] using wordTrace_append hprefix tailTrace_6758495
  have hstable : (prefixWord ++ tailWord_6758495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758495).length < 2 ^ (prefixWord ++ tailWord_6758495).sum := by decide
  have hdescent : baseEnd_6758495 < baseStart_6758495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758592 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 1, 6]
def baseStart_6758592 : Nat := 118140960795 + 6758592 * 2 ^ 59
def prefixEnd_6758592 : Nat := 4983230072969 + 3 ^ 40 * 6758592 * 2
def baseEnd_6758592 : Nat := 1156802081210708737139269

theorem tailTrace_6758592 : CollatzResearch.WordTrace tailWord_6758592 prefixEnd_6758592 1156802081210708737139269 := by
  unfold tailWord_6758592
  simp only [CollatzResearch.WordTrace]
  refine ⟨123253050765391467231067015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164337401020521956308089353 123253050765391467231067015)
  ·
    refine ⟨184879576148087200846600523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123253050765391467231067015 184879576148087200846600523)
    ·
      refine ⟨277319364222130801269900785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184879576148087200846600523 277319364222130801269900785)
      ·
        refine ⟨207989523166598100952425589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277319364222130801269900785 207989523166598100952425589)
        ·
          refine ⟨19499017796868571964289899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207989523166598100952425589 19499017796868571964289899)
          ·
            refine ⟨29248526695302857946434849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19499017796868571964289899 29248526695302857946434849)
            ·
              refine ⟨21936395021477143459826137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29248526695302857946434849 21936395021477143459826137)
              ·
                refine ⟨16452296266107857594869603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21936395021477143459826137 16452296266107857594869603)
                ·
                  refine ⟨24678444399161786392304405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16452296266107857594869603 24678444399161786392304405)
                  ·
                    refine ⟨1156802081210708737139269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24678444399161786392304405 1156802081210708737139269)
                    ·
                      rfl

theorem cell23_6758592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_6758592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758592 prefixEnd_6758592 := by exact prefixLift 6758592
  have htrace : WordTrace (prefixWord ++ tailWord_6758592) baseStart_6758592 baseEnd_6758592 := by
    simpa [prefixWord, tailWord_6758592, baseEnd_6758592] using wordTrace_append hprefix tailTrace_6758592
  have hstable : (prefixWord ++ tailWord_6758592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758592).length < 2 ^ (prefixWord ++ tailWord_6758592).sum := by decide
  have hdescent : baseEnd_6758592 < baseStart_6758592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758595 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 4]
def baseStart_6758595 : Nat := 118140960795 + 6758595 * 2 ^ 59
def prefixEnd_6758595 : Nat := 4983230072969 + 3 ^ 40 * 6758595 * 2
def baseEnd_6758595 : Nat := 3470407784074089699680293

theorem tailTrace_6758595 : CollatzResearch.WordTrace tailWord_6758595 prefixEnd_6758595 3470407784074089699680293 := by
  unfold tailWord_6758595
  simp only [CollatzResearch.WordTrace]
  refine ⟨246506210949772065974493239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164337473966514710649662159 246506210949772065974493239)
  ·
    refine ⟨369759316424658098961739859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246506210949772065974493239 369759316424658098961739859)
    ·
      refine ⟨554638974636987148442609789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369759316424658098961739859 554638974636987148442609789)
      ·
        refine ⟨207989615488870180665978671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 554638974636987148442609789 207989615488870180665978671)
        ·
          refine ⟨311984423233305270998968007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207989615488870180665978671 311984423233305270998968007)
          ·
            refine ⟨467976634849957906498452011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311984423233305270998968007 467976634849957906498452011)
            ·
              refine ⟨701964952274936859747678017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467976634849957906498452011 701964952274936859747678017)
              ·
                refine ⟨526473714206202644810758513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701964952274936859747678017 526473714206202644810758513)
                ·
                  refine ⟨394855285654651983608068885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526473714206202644810758513 394855285654651983608068885)
                  ·
                    refine ⟨18508841515061811731628229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 394855285654651983608068885 18508841515061811731628229)
                    ·
                      refine ⟨3470407784074089699680293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18508841515061811731628229 3470407784074089699680293)
                      ·
                        rfl

theorem cell23_6758595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_6758595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758595 prefixEnd_6758595 := by exact prefixLift 6758595
  have htrace : WordTrace (prefixWord ++ tailWord_6758595) baseStart_6758595 baseEnd_6758595 := by
    simpa [prefixWord, tailWord_6758595, baseEnd_6758595] using wordTrace_append hprefix tailTrace_6758595
  have hstable : (prefixWord ++ tailWord_6758595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758595).length < 2 ^ (prefixWord ++ tailWord_6758595).sum := by decide
  have hdescent : baseEnd_6758595 < baseStart_6758595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758596 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_6758596 : Nat := 118140960795 + 6758596 * 2 ^ 59
def prefixEnd_6758596 : Nat := 4983230072969 + 3 ^ 40 * 6758596 * 2
def baseEnd_6758596 : Nat := 1156802765851581398589263

theorem tailTrace_6758596 : CollatzResearch.WordTrace tailWord_6758596 prefixEnd_6758596 1156802765851581398589263 := by
  unfold tailWord_6758596
  simp only [CollatzResearch.WordTrace]
  refine ⟨123253123711384221572639821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164337498281845628763519761 123253123711384221572639821)
  ·
    refine ⟨46219921391769083089739933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123253123711384221572639821 46219921391769083089739933)
    ·
      refine ⟨17332470521913406158652475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46219921391769083089739933 17332470521913406158652475)
      ·
        refine ⟨25998705782870109237978713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17332470521913406158652475 25998705782870109237978713)
        ·
          refine ⟨19499029337152581928484035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25998705782870109237978713 19499029337152581928484035)
          ·
            refine ⟨29248544005728872892726053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19499029337152581928484035 29248544005728872892726053)
            ·
              refine ⟨5484102001074163667386135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29248544005728872892726053 5484102001074163667386135)
              ·
                refine ⟨8226153001611245501079203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484102001074163667386135 8226153001611245501079203)
                ·
                  refine ⟨12339229502416868251618805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8226153001611245501079203 12339229502416868251618805)
                  ·
                    refine ⟨1156802765851581398589263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12339229502416868251618805 1156802765851581398589263)
                    ·
                      rfl

theorem cell23_6758596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_6758596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758596 prefixEnd_6758596 := by exact prefixLift 6758596
  have htrace : WordTrace (prefixWord ++ tailWord_6758596) baseStart_6758596 baseEnd_6758596 := by
    simpa [prefixWord, tailWord_6758596, baseEnd_6758596] using wordTrace_append hprefix tailTrace_6758596
  have hstable : (prefixWord ++ tailWord_6758596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758596).length < 2 ^ (prefixWord ++ tailWord_6758596).sum := by decide
  have hdescent : baseEnd_6758596 < baseStart_6758596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758602 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_6758602 : Nat := 118140960795 + 6758602 * 2 ^ 59
def prefixEnd_6758602 : Nat := 4983230072969 + 3 ^ 40 * 6758602 * 2
def baseEnd_6758602 : Nat := 3470411378438671172292761

theorem tailTrace_6758602 : CollatzResearch.WordTrace tailWord_6758602 prefixEnd_6758602 3470411378438671172292761 := by
  unfold tailWord_6758602
  simp only [CollatzResearch.WordTrace]
  refine ⟨61626616565186676542499515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164337644173831137446665373 61626616565186676542499515)
  ·
    refine ⟨92439924847780014813749273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61626616565186676542499515 92439924847780014813749273)
    ·
      refine ⟨69329943635835011110311955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92439924847780014813749273 69329943635835011110311955)
      ·
        refine ⟨103994915453752516665467933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69329943635835011110311955 103994915453752516665467933)
        ·
          refine ⟨38998093295157193749550475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103994915453752516665467933 38998093295157193749550475)
          ·
            refine ⟨58497139942735790624325713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38998093295157193749550475 58497139942735790624325713)
            ·
              refine ⟨43872854957051842968244285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58497139942735790624325713 43872854957051842968244285)
              ·
                refine ⟨16452320608894441113091607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43872854957051842968244285 16452320608894441113091607)
                ·
                  refine ⟨24678480913341661669637411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16452320608894441113091607 24678480913341661669637411)
                  ·
                    refine ⟨37017721370012492504456117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24678480913341661669637411 37017721370012492504456117)
                    ·
                      refine ⟨3470411378438671172292761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37017721370012492504456117 3470411378438671172292761)
                      ·
                        rfl

theorem cell23_6758602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_6758602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758602 prefixEnd_6758602 := by exact prefixLift 6758602
  have htrace : WordTrace (prefixWord ++ tailWord_6758602) baseStart_6758602 baseEnd_6758602 := by
    simpa [prefixWord, tailWord_6758602, baseEnd_6758602] using wordTrace_append hprefix tailTrace_6758602
  have hstable : (prefixWord ++ tailWord_6758602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758602).length < 2 ^ (prefixWord ++ tailWord_6758602).sum := by decide
  have hdescent : baseEnd_6758602 < baseStart_6758602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758609 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 2, 4]
def baseStart_6758609 : Nat := 118140960795 + 6758609 * 2 ^ 59
def prefixEnd_6758609 : Nat := 4983230072969 + 3 ^ 40 * 6758609 * 2
def baseEnd_6758609 : Nat := 1156804990934417548301743

theorem tailTrace_6758609 : CollatzResearch.WordTrace tailWord_6758609 prefixEnd_6758609 1156804990934417548301743 := by
  unfold tailWord_6758609
  simp only [CollatzResearch.WordTrace]
  refine ⟨246506721571721346365502881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164337814381147564243668587 246506721571721346365502881)
  ·
    refine ⟨184880041178791009774127161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246506721571721346365502881 184880041178791009774127161)
    ·
      refine ⟨138660030884093257330595371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184880041178791009774127161 138660030884093257330595371)
      ·
        refine ⟨207990046326139885995893057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138660030884093257330595371 207990046326139885995893057)
        ·
          refine ⟨155992534744604914496919793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207990046326139885995893057 155992534744604914496919793)
          ·
            refine ⟨116994401058453685872689845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155992534744604914496919793 116994401058453685872689845)
            ·
              refine ⟨10968225099230033050564673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116994401058453685872689845 10968225099230033050564673)
              ·
                refine ⟨8226168824422524787923505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10968225099230033050564673 8226168824422524787923505)
                ·
                  refine ⟨6169626618316893590942629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8226168824422524787923505 6169626618316893590942629)
                  ·
                    refine ⟨1156804990934417548301743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6169626618316893590942629 1156804990934417548301743)
                    ·
                      rfl

theorem cell23_6758609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_6758609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758609 prefixEnd_6758609 := by exact prefixLift 6758609
  have htrace : WordTrace (prefixWord ++ tailWord_6758609) baseStart_6758609 baseEnd_6758609 := by
    simpa [prefixWord, tailWord_6758609, baseEnd_6758609] using wordTrace_append hprefix tailTrace_6758609
  have hstable : (prefixWord ++ tailWord_6758609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758609).length < 2 ^ (prefixWord ++ tailWord_6758609).sum := by decide
  have hdescent : baseEnd_6758609 < baseStart_6758609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758615 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_6758615 : Nat := 118140960795 + 6758615 * 2 ^ 59
def prefixEnd_6758615 : Nat := 4983230072969 + 3 ^ 40 * 6758615 * 2
def baseEnd_6758615 : Nat := 3470418053687179621430201

theorem tailTrace_6758615 : CollatzResearch.WordTrace tailWord_6758615 prefixEnd_6758615 3470418053687179621430201 := by
  unfold tailWord_6758615
  simp only [CollatzResearch.WordTrace]
  refine ⟨246506940409699609390221299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164337960273133072926814199 246506940409699609390221299)
  ·
    refine ⟨369760410614549414085331949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246506940409699609390221299 369760410614549414085331949)
    ·
      refine ⟨138660153980456030281999481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369760410614549414085331949 138660153980456030281999481)
      ·
        refine ⟨103995115485342022711499611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138660153980456030281999481 103995115485342022711499611)
        ·
          refine ⟨155992673228013034067249417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103995115485342022711499611 155992673228013034067249417)
          ·
            refine ⟨116994504921009775550437063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155992673228013034067249417 116994504921009775550437063)
            ·
              refine ⟨175491757381514663325655595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116994504921009775550437063 175491757381514663325655595)
              ·
                refine ⟨263237636072271994988483393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175491757381514663325655595 263237636072271994988483393)
                ·
                  refine ⟨197428227054203996241362545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263237636072271994988483393 197428227054203996241362545)
                  ·
                    refine ⟨148071170290652997181021909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197428227054203996241362545 148071170290652997181021909)
                    ·
                      refine ⟨3470418053687179621430201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148071170290652997181021909 3470418053687179621430201)
                      ·
                        rfl

theorem cell23_6758615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_6758615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758615 prefixEnd_6758615 := by exact prefixLift 6758615
  have htrace : WordTrace (prefixWord ++ tailWord_6758615) baseStart_6758615 baseEnd_6758615 := by
    simpa [prefixWord, tailWord_6758615, baseEnd_6758615] using wordTrace_append hprefix tailTrace_6758615
  have hstable : (prefixWord ++ tailWord_6758615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758615).length < 2 ^ (prefixWord ++ tailWord_6758615).sum := by decide
  have hdescent : baseEnd_6758615 < baseStart_6758615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758616 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 3, 2, 2]
def baseStart_6758616 : Nat := 118140960795 + 6758616 * 2 ^ 59
def prefixEnd_6758616 : Nat := 4983230072969 + 3 ^ 40 * 6758616 * 2
def baseEnd_6758616 : Nat := 3470418567167834117517697

theorem tailTrace_6758616 : CollatzResearch.WordTrace tailWord_6758616 prefixEnd_6758616 3470418567167834117517697 := by
  unfold tailWord_6758616
  simp only [CollatzResearch.WordTrace]
  refine ⟨123253488441347993280503851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164337984588463991040671801 123253488441347993280503851)
  ·
    refine ⟨184880232662021989920755777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123253488441347993280503851 184880232662021989920755777)
    ·
      refine ⟨138660174496516492440566833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184880232662021989920755777 138660174496516492440566833)
      ·
        refine ⟨103995130872387369330425125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138660174496516492440566833 103995130872387369330425125)
        ·
          refine ⟨19499087038572631749454711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103995130872387369330425125 19499087038572631749454711)
          ·
            refine ⟨29248630557858947624182067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19499087038572631749454711 29248630557858947624182067)
            ·
              refine ⟨43872945836788421436273101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29248630557858947624182067 43872945836788421436273101)
              ·
                refine ⟨16452354688795658038602413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43872945836788421436273101 16452354688795658038602413)
                ·
                  refine ⟨6169633008298371764475905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16452354688795658038602413 6169633008298371764475905)
                  ·
                    refine ⟨4627224756223778823356929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6169633008298371764475905 4627224756223778823356929)
                    ·
                      refine ⟨3470418567167834117517697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627224756223778823356929 3470418567167834117517697)
                      ·
                        rfl

theorem cell23_6758616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_6758616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758616 prefixEnd_6758616 := by exact prefixLift 6758616
  have htrace : WordTrace (prefixWord ++ tailWord_6758616) baseStart_6758616 baseEnd_6758616 := by
    simpa [prefixWord, tailWord_6758616, baseEnd_6758616] using wordTrace_append hprefix tailTrace_6758616
  have hstable : (prefixWord ++ tailWord_6758616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758616).length < 2 ^ (prefixWord ++ tailWord_6758616).sum := by decide
  have hdescent : baseEnd_6758616 < baseStart_6758616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758629 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_6758629 : Nat := 118140960795 + 6758629 * 2 ^ 59
def prefixEnd_6758629 : Nat := 4983230072969 + 3 ^ 40 * 6758629 * 2
def baseEnd_6758629 : Nat := 3470425242416342566655137

theorem tailTrace_6758629 : CollatzResearch.WordTrace tailWord_6758629 prefixEnd_6758629 3470425242416342566655137 := by
  unfold tailWord_6758629
  simp only [CollatzResearch.WordTrace]
  refine ⟨246507451031648889781230941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164338300687765926520820627 246507451031648889781230941)
  ·
    refine ⟨92440294136868333667961603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246507451031648889781230941 92440294136868333667961603)
    ·
      refine ⟨138660441205302500501942405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92440294136868333667961603 138660441205302500501942405)
      ·
        refine ⟨25998832725994218844114201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138660441205302500501942405 25998832725994218844114201)
        ·
          refine ⟨19499124544495664133085651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25998832725994218844114201 19499124544495664133085651)
          ·
            refine ⟨29248686816743496199628477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19499124544495664133085651 29248686816743496199628477)
            ·
              refine ⟨10968257556278811074860679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29248686816743496199628477 10968257556278811074860679)
              ·
                refine ⟨16452386334418216612291019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10968257556278811074860679 16452386334418216612291019)
                ·
                  refine ⟨24678579501627324918436529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16452386334418216612291019 24678579501627324918436529)
                  ·
                    refine ⟨18508934626220493688827397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24678579501627324918436529 18508934626220493688827397)
                    ·
                      refine ⟨3470425242416342566655137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18508934626220493688827397 3470425242416342566655137)
                      ·
                        rfl

theorem cell23_6758629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_6758629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758629 prefixEnd_6758629 := by exact prefixLift 6758629
  have htrace : WordTrace (prefixWord ++ tailWord_6758629) baseStart_6758629 baseEnd_6758629 := by
    simpa [prefixWord, tailWord_6758629, baseEnd_6758629] using wordTrace_append hprefix tailTrace_6758629
  have hstable : (prefixWord ++ tailWord_6758629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758629).length < 2 ^ (prefixWord ++ tailWord_6758629).sum := by decide
  have hdescent : baseEnd_6758629 < baseStart_6758629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758639 : List Nat := [1, 1, 2, 1, 6, 3, 2, 7]
def baseStart_6758639 : Nat := 118140960795 + 6758639 * 2 ^ 59
def prefixEnd_6758639 : Nat := 4983230072969 + 3 ^ 40 * 6758639 * 2
def baseEnd_6758639 : Nat := 128534458415662501019633

theorem tailTrace_6758639 : CollatzResearch.WordTrace tailWord_6758639 prefixEnd_6758639 128534458415662501019633 := by
  unfold tailWord_6758639
  simp only [CollatzResearch.WordTrace]
  refine ⟨246507815761612661489094971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164338543841075107659396647 246507815761612661489094971)
  ·
    refine ⟨369761723642418992233642457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246507815761612661489094971 369761723642418992233642457)
    ·
      refine ⟨277321292731814244175231843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369761723642418992233642457 277321292731814244175231843)
      ·
        refine ⟨415981939097721366262847765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277321292731814244175231843 415981939097721366262847765)
        ·
          refine ⟨19499153395205689043570989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 415981939097721366262847765 19499153395205689043570989)
          ·
            refine ⟨7312182523202133391339121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19499153395205689043570989 7312182523202133391339121)
            ·
              refine ⟨5484136892401600043504341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7312182523202133391339121 5484136892401600043504341)
              ·
                refine ⟨128534458415662501019633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5484136892401600043504341 128534458415662501019633)
                ·
                  rfl

theorem cell23_6758639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 7].length) (baseStart_6758639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758639 prefixEnd_6758639 := by exact prefixLift 6758639
  have htrace : WordTrace (prefixWord ++ tailWord_6758639) baseStart_6758639 baseEnd_6758639 := by
    simpa [prefixWord, tailWord_6758639, baseEnd_6758639] using wordTrace_append hprefix tailTrace_6758639
  have hstable : (prefixWord ++ tailWord_6758639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758639).length < 2 ^ (prefixWord ++ tailWord_6758639).sum := by decide
  have hdescent : baseEnd_6758639 < baseStart_6758639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758650 : List Nat := [3, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2]
def baseStart_6758650 : Nat := 118140960795 + 6758650 * 2 ^ 59
def prefixEnd_6758650 : Nat := 4983230072969 + 3 ^ 40 * 6758650 * 2
def baseEnd_6758650 : Nat := 3470436025510086984492541

theorem tailTrace_6758650 : CollatzResearch.WordTrace tailWord_6758650 prefixEnd_6758650 3470436025510086984492541 := by
  unfold tailWord_6758650
  simp only [CollatzResearch.WordTrace]
  refine ⟨61627054241143202591936351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164338811309715206911830269 61627054241143202591936351)
  ·
    refine ⟨92440581361714803887904527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61627054241143202591936351 92440581361714803887904527)
    ·
      refine ⟨138660872042572205831856791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92440581361714803887904527 138660872042572205831856791)
      ·
        refine ⟨207991308063858308747785187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138660872042572205831856791 207991308063858308747785187)
        ·
          refine ⟨311986962095787463121677781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207991308063858308747785187 311986962095787463121677781)
          ·
            refine ⟨7312194424120018666914323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 311986962095787463121677781 7312194424120018666914323)
            ·
              refine ⟨10968291636180028000371485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312194424120018666914323 10968291636180028000371485)
              ·
                refine ⟨4113109363567510500139307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10968291636180028000371485 4113109363567510500139307)
                ·
                  refine ⟨6169664045351265750208961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113109363567510500139307 6169664045351265750208961)
                  ·
                    refine ⟨4627248034013449312656721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6169664045351265750208961 4627248034013449312656721)
                    ·
                      refine ⟨3470436025510086984492541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627248034013449312656721 3470436025510086984492541)
                      ·
                        rfl

theorem cell23_6758650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2].length) (baseStart_6758650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758650 prefixEnd_6758650 := by exact prefixLift 6758650
  have htrace : WordTrace (prefixWord ++ tailWord_6758650) baseStart_6758650 baseEnd_6758650 := by
    simpa [prefixWord, tailWord_6758650, baseEnd_6758650] using wordTrace_append hprefix tailTrace_6758650
  have hstable : (prefixWord ++ tailWord_6758650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758650).length < 2 ^ (prefixWord ++ tailWord_6758650).sum := by decide
  have hdescent : baseEnd_6758650 < baseStart_6758650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758759 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 1, 7]
def baseStart_6758759 : Nat := 118140960795 + 6758759 * 2 ^ 59
def prefixEnd_6758759 : Nat := 4983230072969 + 3 ^ 40 * 6758759 * 2
def baseEnd_6758759 : Nat := 1156830664967142352676513

theorem tailTrace_6758759 : CollatzResearch.WordTrace tailWord_6758759 prefixEnd_6758759 1156830664967142352676513 := by
  unfold tailWord_6758759
  simp only [CollatzResearch.WordTrace]
  refine ⟨246512192521177921983463331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164341461680785281322308887 246512192521177921983463331)
  ·
    refine ⟨369768288781766882975194997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246512192521177921983463331 369768288781766882975194997)
    ·
      refine ⟨34665777073290645278924531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 369768288781766882975194997 34665777073290645278924531)
      ·
        refine ⟨51998665609935967918386797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34665777073290645278924531 51998665609935967918386797)
        ·
          refine ⟨19499499603725987969395049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51998665609935967918386797 19499499603725987969395049)
          ·
            refine ⟨14624624702794490977046287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19499499603725987969395049 14624624702794490977046287)
            ·
              refine ⟨21936937054191736465569431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14624624702794490977046287 21936937054191736465569431)
              ·
                refine ⟨32905405581287604698354147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21936937054191736465569431 32905405581287604698354147)
                ·
                  refine ⟨49358108371931407047531221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32905405581287604698354147 49358108371931407047531221)
                  ·
                    refine ⟨1156830664967142352676513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49358108371931407047531221 1156830664967142352676513)
                    ·
                      rfl

theorem cell23_6758759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_6758759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758759 prefixEnd_6758759 := by exact prefixLift 6758759
  have htrace : WordTrace (prefixWord ++ tailWord_6758759) baseStart_6758759 baseEnd_6758759 := by
    simpa [prefixWord, tailWord_6758759, baseEnd_6758759] using wordTrace_append hprefix tailTrace_6758759
  have hstable : (prefixWord ++ tailWord_6758759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758759).length < 2 ^ (prefixWord ++ tailWord_6758759).sum := by decide
  have hdescent : baseEnd_6758759 < baseStart_6758759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758774 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6758774 : Nat := 118140960795 + 6758774 * 2 ^ 59
def prefixEnd_6758774 : Nat := 4983230072969 + 3 ^ 40 * 6758774 * 2
def baseEnd_6758774 : Nat := 3470499697111244499341971

theorem tailTrace_6758774 : CollatzResearch.WordTrace tailWord_6758774 prefixEnd_6758774 3470499697111244499341971 := by
  unfold tailWord_6758774
  simp only [CollatzResearch.WordTrace]
  refine ⟨15407046226007723721578711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164341826410749053030172917 15407046226007723721578711)
  ·
    refine ⟨23110569339011585582368067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15407046226007723721578711 23110569339011585582368067)
    ·
      refine ⟨34665854008517378373552101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23110569339011585582368067 34665854008517378373552101)
      ·
        refine ⟨6499847626597008445041019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34665854008517378373552101 6499847626597008445041019)
        ·
          refine ⟨9749771439895512667561529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6499847626597008445041019 9749771439895512667561529)
          ·
            refine ⟨7312328579921634500671147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9749771439895512667561529 7312328579921634500671147)
            ·
              refine ⟨10968492869882451751006721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312328579921634500671147 10968492869882451751006721)
              ·
                refine ⟨8226369652411838813255041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10968492869882451751006721 8226369652411838813255041)
                ·
                  refine ⟨6169777239308879109941281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8226369652411838813255041 6169777239308879109941281)
                  ·
                    refine ⟨4627332929481659332455961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6169777239308879109941281 4627332929481659332455961)
                    ·
                      refine ⟨3470499697111244499341971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627332929481659332455961 3470499697111244499341971)
                      ·
                        rfl

theorem cell23_6758774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6758774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758774 prefixEnd_6758774 := by exact prefixLift 6758774
  have htrace : WordTrace (prefixWord ++ tailWord_6758774) baseStart_6758774 baseEnd_6758774 := by
    simpa [prefixWord, tailWord_6758774, baseEnd_6758774] using wordTrace_append hprefix tailTrace_6758774
  have hstable : (prefixWord ++ tailWord_6758774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758774).length < 2 ^ (prefixWord ++ tailWord_6758774).sum := by decide
  have hdescent : baseEnd_6758774 < baseStart_6758774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758796 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 2, 4, 2]
def baseStart_6758796 : Nat := 118140960795 + 6758796 * 2 ^ 59
def prefixEnd_6758796 : Nat := 4983230072969 + 3 ^ 40 * 6758796 * 2
def baseEnd_6758796 : Nat := 3470510993685643413266869

theorem tailTrace_6758796 : CollatzResearch.WordTrace tailWord_6758796 prefixEnd_6758796 3470510993685643413266869 := by
  unfold tailWord_6758796
  simp only [CollatzResearch.WordTrace]
  refine ⟨123256771011021938651280121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164342361348029251535040161 123256771011021938651280121)
  ·
    refine ⟨92442578258266453988460091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123256771011021938651280121 92442578258266453988460091)
    ·
      refine ⟨138663867387399680982690137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92442578258266453988460091 138663867387399680982690137)
      ·
        refine ⟨103997900540549760737017603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138663867387399680982690137 103997900540549760737017603)
        ·
          refine ⟨155996850810824641105526405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103997900540549760737017603 155996850810824641105526405)
          ·
            refine ⟨29249409527029620207286201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155996850810824641105526405 29249409527029620207286201)
            ·
              refine ⟨21937057145272215155464651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29249409527029620207286201 21937057145272215155464651)
              ·
                refine ⟨32905585717908322733196977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21937057145272215155464651 32905585717908322733196977)
                ·
                  refine ⟨24679189288431242049897733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32905585717908322733196977 24679189288431242049897733)
                  ·
                    refine ⟨4627347991580857884355825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24679189288431242049897733 4627347991580857884355825)
                    ·
                      refine ⟨3470510993685643413266869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627347991580857884355825 3470510993685643413266869)
                      ·
                        rfl

theorem cell23_6758796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_6758796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758796 prefixEnd_6758796 := by exact prefixLift 6758796
  have htrace : WordTrace (prefixWord ++ tailWord_6758796) baseStart_6758796 baseEnd_6758796 := by
    simpa [prefixWord, tailWord_6758796, baseEnd_6758796] using wordTrace_append hprefix tailTrace_6758796
  have hstable : (prefixWord ++ tailWord_6758796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758796).length < 2 ^ (prefixWord ++ tailWord_6758796).sum := by decide
  have hdescent : baseEnd_6758796 < baseStart_6758796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758832 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 11]
def baseStart_6758832 : Nat := 118140960795 + 6758832 * 2 ^ 59
def prefixEnd_6758832 : Nat := 4983230072969 + 3 ^ 40 * 6758832 * 2
def baseEnd_6758832 : Nat := 1156843159663068424138901

theorem tailTrace_6758832 : CollatzResearch.WordTrace tailWord_6758832 prefixEnd_6758832 1156843159663068424138901 := by
  unfold tailWord_6758832
  simp only [CollatzResearch.WordTrace]
  refine ⟨123257427524956727725435375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164343236699942303633913833 123257427524956727725435375)
  ·
    refine ⟨184886141287435091588153063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123257427524956727725435375 184886141287435091588153063)
    ·
      refine ⟨277329211931152637382229595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184886141287435091588153063 277329211931152637382229595)
      ·
        refine ⟨415993817896728956073344393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277329211931152637382229595 415993817896728956073344393)
        ·
          refine ⟨311995363422546717055008295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415993817896728956073344393 311995363422546717055008295)
          ·
            refine ⟨467993045133820075582512443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311995363422546717055008295 467993045133820075582512443)
            ·
              refine ⟨701989567700730113373768665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467993045133820075582512443 701989567700730113373768665)
              ·
                refine ⟨526492175775547585030326499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701989567700730113373768665 526492175775547585030326499)
                ·
                  refine ⟨789738263663321377545489749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526492175775547585030326499 789738263663321377545489749)
                  ·
                    refine ⟨1156843159663068424138901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 789738263663321377545489749 1156843159663068424138901)
                    ·
                      rfl

theorem cell23_6758832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_6758832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758832 prefixEnd_6758832 := by exact prefixLift 6758832
  have htrace : WordTrace (prefixWord ++ tailWord_6758832) baseStart_6758832 baseEnd_6758832 := by
    simpa [prefixWord, tailWord_6758832, baseEnd_6758832] using wordTrace_append hprefix tailTrace_6758832
  have hstable : (prefixWord ++ tailWord_6758832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758832).length < 2 ^ (prefixWord ++ tailWord_6758832).sum := by decide
  have hdescent : baseEnd_6758832 < baseStart_6758832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758873 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 2, 3, 2]
def baseStart_6758873 : Nat := 118140960795 + 6758873 * 2 ^ 59
def prefixEnd_6758873 : Nat := 4983230072969 + 3 ^ 40 * 6758873 * 2
def baseEnd_6758873 : Nat := 3470550531696039612004015

theorem tailTrace_6758873 : CollatzResearch.WordTrace tailWord_6758873 prefixEnd_6758873 3470550531696039612004015 := by
  unfold tailWord_6758873
  simp only [CollatzResearch.WordTrace]
  refine ⟨246516350442764919453113273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164344233628509946302075515 246516350442764919453113273)
  ·
    refine ⟨184887262832073689589834955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246516350442764919453113273 184887262832073689589834955)
    ·
      refine ⟨277330894248110534384752433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184887262832073689589834955 277330894248110534384752433)
      ·
        refine ⟨207998170686082900788564325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277330894248110534384752433 207998170686082900788564325)
        ·
          refine ⟨38999657003640543897855811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207998170686082900788564325 38999657003640543897855811)
          ·
            refine ⟨58499485505460815846783717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38999657003640543897855811 58499485505460815846783717)
            ·
              refine ⟨10968653532273902971271947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58499485505460815846783717 10968653532273902971271947)
              ·
                refine ⟨16452980298410854456907921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10968653532273902971271947 16452980298410854456907921)
                ·
                  refine ⟨12339735223808140842680941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16452980298410854456907921 12339735223808140842680941)
                  ·
                    refine ⟨4627400708928052816005353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12339735223808140842680941 4627400708928052816005353)
                    ·
                      refine ⟨3470550531696039612004015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627400708928052816005353 3470550531696039612004015)
                      ·
                        rfl

theorem cell23_6758873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_6758873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758873 prefixEnd_6758873 := by exact prefixLift 6758873
  have htrace : WordTrace (prefixWord ++ tailWord_6758873) baseStart_6758873 baseEnd_6758873 := by
    simpa [prefixWord, tailWord_6758873, baseEnd_6758873] using wordTrace_append hprefix tailTrace_6758873
  have hstable : (prefixWord ++ tailWord_6758873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758873).length < 2 ^ (prefixWord ++ tailWord_6758873).sum := by decide
  have hdescent : baseEnd_6758873 < baseStart_6758873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758879 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 3, 6]
def baseStart_6758879 : Nat := 118140960795 + 6758879 * 2 ^ 59
def prefixEnd_6758879 : Nat := 4983230072969 + 3 ^ 40 * 6758879 * 2
def baseEnd_6758879 : Nat := 1156851204193322196176329

theorem tailTrace_6758879 : CollatzResearch.WordTrace tailWord_6758879 prefixEnd_6758879 1156851204193322196176329 := by
  unfold tailWord_6758879
  simp only [CollatzResearch.WordTrace]
  refine ⟨246516569280743182477831691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164344379520495454985221127 246516569280743182477831691)
  ·
    refine ⟨369774853921114773716747537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246516569280743182477831691 369774853921114773716747537)
    ·
      refine ⟨277331140440836080287560653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369774853921114773716747537 277331140440836080287560653)
      ·
        refine ⟨103999177665313530107835245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277331140440836080287560653 103999177665313530107835245)
        ·
          refine ⟨38999691624492573790438217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103999177665313530107835245 38999691624492573790438217)
          ·
            refine ⟨29249768718369430342828663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38999691624492573790438217 29249768718369430342828663)
            ·
              refine ⟨43874653077554145514242995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29249768718369430342828663 43874653077554145514242995)
              ·
                refine ⟨65811979616331218271364493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43874653077554145514242995 65811979616331218271364493)
                ·
                  refine ⟨24679492356124206851761685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65811979616331218271364493 24679492356124206851761685)
                  ·
                    refine ⟨1156851204193322196176329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24679492356124206851761685 1156851204193322196176329)
                    ·
                      rfl

theorem cell23_6758879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_6758879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758879 prefixEnd_6758879 := by exact prefixLift 6758879
  have htrace : WordTrace (prefixWord ++ tailWord_6758879) baseStart_6758879 baseEnd_6758879 := by
    simpa [prefixWord, tailWord_6758879, baseEnd_6758879] using wordTrace_append hprefix tailTrace_6758879
  have hstable : (prefixWord ++ tailWord_6758879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758879).length < 2 ^ (prefixWord ++ tailWord_6758879).sum := by decide
  have hdescent : baseEnd_6758879 < baseStart_6758879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758889 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_6758889 : Nat := 118140960795 + 6758889 * 2 ^ 59
def prefixEnd_6758889 : Nat := 4983230072969 + 3 ^ 40 * 6758889 * 2
def baseEnd_6758889 : Nat := 3470558747386511549403941

theorem tailTrace_6758889 : CollatzResearch.WordTrace tailWord_6758889 prefixEnd_6758889 3470558747386511549403941 := by
  unfold tailWord_6758889
  simp only [CollatzResearch.WordTrace]
  refine ⟨246516934010706954185695721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164344622673804636123797147 246516934010706954185695721)
  ·
    refine ⟨184887700508030215639271791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246516934010706954185695721 184887700508030215639271791)
    ·
      refine ⟨277331550762045323458907687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184887700508030215639271791 277331550762045323458907687)
      ·
        refine ⟨415997326143067985188361531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277331550762045323458907687 415997326143067985188361531)
        ·
          refine ⟨623995989214601977782542297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415997326143067985188361531 623995989214601977782542297)
          ·
            refine ⟨467996991910951483336906723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623995989214601977782542297 467996991910951483336906723)
            ·
              refine ⟨701995487866427225005360085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467996991910951483336906723 701995487866427225005360085)
              ·
                refine ⟨16453019246869388086063127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 701995487866427225005360085 16453019246869388086063127)
                ·
                  refine ⟨24679528870304082129094691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16453019246869388086063127 24679528870304082129094691)
                  ·
                    refine ⟨37019293305456123193642037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24679528870304082129094691 37019293305456123193642037)
                    ·
                      refine ⟨3470558747386511549403941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37019293305456123193642037 3470558747386511549403941)
                      ·
                        rfl

theorem cell23_6758889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_6758889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758889 prefixEnd_6758889 := by exact prefixLift 6758889
  have htrace : WordTrace (prefixWord ++ tailWord_6758889) baseStart_6758889 baseEnd_6758889 := by
    simpa [prefixWord, tailWord_6758889, baseEnd_6758889] using wordTrace_append hprefix tailTrace_6758889
  have hstable : (prefixWord ++ tailWord_6758889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758889).length < 2 ^ (prefixWord ++ tailWord_6758889).sum := by decide
  have hdescent : baseEnd_6758889 < baseStart_6758889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758899 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 4]
def baseStart_6758899 : Nat := 118140960795 + 6758899 * 2 ^ 59
def prefixEnd_6758899 : Nat := 4983230072969 + 3 ^ 40 * 6758899 * 2
def baseEnd_6758899 : Nat := 3470563882193056510278895

theorem tailTrace_6758899 : CollatzResearch.WordTrace tailWord_6758899 prefixEnd_6758899 3470563882193056510278895 := by
  unfold tailWord_6758899
  simp only [CollatzResearch.WordTrace]
  refine ⟨246517298740670725893559751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164344865827113817262373167 246517298740670725893559751)
  ·
    refine ⟨369775948111006088840339627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246517298740670725893559751 369775948111006088840339627)
    ·
      refine ⟨554663922166509133260509441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369775948111006088840339627 554663922166509133260509441)
      ·
        refine ⟨415997941624881849945382081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554663922166509133260509441 415997941624881849945382081)
        ·
          refine ⟨311998456218661387459036561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415997941624881849945382081 311998456218661387459036561)
          ·
            refine ⟨233998842163996040594277421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311998456218661387459036561 233998842163996040594277421)
            ·
              refine ⟨87749565811498515222854033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233998842163996040594277421 87749565811498515222854033)
              ·
                refine ⟨65812174358623886417140525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87749565811498515222854033 65812174358623886417140525)
                ·
                  refine ⟨24679565384483957406427697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65812174358623886417140525 24679565384483957406427697)
                  ·
                    refine ⟨18509674038362968054820773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24679565384483957406427697 18509674038362968054820773)
                    ·
                      refine ⟨3470563882193056510278895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18509674038362968054820773 3470563882193056510278895)
                      ·
                        rfl

theorem cell23_6758899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_6758899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758899 prefixEnd_6758899 := by exact prefixLift 6758899
  have htrace : WordTrace (prefixWord ++ tailWord_6758899) baseStart_6758899 baseEnd_6758899 := by
    simpa [prefixWord, tailWord_6758899, baseEnd_6758899] using wordTrace_append hprefix tailTrace_6758899
  have hstable : (prefixWord ++ tailWord_6758899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758899).length < 2 ^ (prefixWord ++ tailWord_6758899).sum := by decide
  have hdescent : baseEnd_6758899 < baseStart_6758899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758913 : List Nat := [1, 2, 4, 1, 3, 1, 2, 3, 2, 4]
def baseStart_6758913 : Nat := 118140960795 + 6758913 * 2 ^ 59
def prefixEnd_6758913 : Nat := 4983230072969 + 3 ^ 40 * 6758913 * 2
def baseEnd_6758913 : Nat := 1156857023640739818501277

theorem tailTrace_6758913 : CollatzResearch.WordTrace tailWord_6758913 prefixEnd_6758913 1156857023640739818501277 := by
  unfold tailWord_6758913
  simp only [CollatzResearch.WordTrace]
  refine ⟨246517809362620006284569393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164345206241746670856379595 246517809362620006284569393)
  ·
    refine ⟨184888357021965004713427045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246517809362620006284569393 184888357021965004713427045)
    ·
      refine ⟨34666566941618438383767571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184888357021965004713427045 34666566941618438383767571)
      ·
        refine ⟨51999850412427657575651357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34666566941618438383767571 51999850412427657575651357)
        ·
          refine ⟨19499943904660371590869259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51999850412427657575651357 19499943904660371590869259)
          ·
            refine ⟨29249915856990557386303889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19499943904660371590869259 29249915856990557386303889)
            ·
              refine ⟨21937436892742918039727917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29249915856990557386303889 21937436892742918039727917)
              ·
                refine ⟨8226538834778594264897969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21937436892742918039727917 8226538834778594264897969)
                ·
                  refine ⟨6169904126083945698673477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8226538834778594264897969 6169904126083945698673477)
                  ·
                    refine ⟨1156857023640739818501277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6169904126083945698673477 1156857023640739818501277)
                    ·
                      rfl

theorem cell23_6758913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_6758913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758913 prefixEnd_6758913 := by exact prefixLift 6758913
  have htrace : WordTrace (prefixWord ++ tailWord_6758913) baseStart_6758913 baseEnd_6758913 := by
    simpa [prefixWord, tailWord_6758913, baseEnd_6758913] using wordTrace_append hprefix tailTrace_6758913
  have hstable : (prefixWord ++ tailWord_6758913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758913).length < 2 ^ (prefixWord ++ tailWord_6758913).sum := by decide
  have hdescent : baseEnd_6758913 < baseStart_6758913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758940 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_6758940 : Nat := 118140960795 + 6758940 * 2 ^ 59
def prefixEnd_6758940 : Nat := 4983230072969 + 3 ^ 40 * 6758940 * 2
def baseEnd_6758940 : Nat := 3470584934899890849866207

theorem tailTrace_6758940 : CollatzResearch.WordTrace tailWord_6758940 prefixEnd_6758940 3470584934899890849866207 := by
  unfold tailWord_6758940
  simp only [CollatzResearch.WordTrace]
  refine ⟨123259397066761094947901137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164345862755681459930534849 123259397066761094947901137)
  ·
    refine ⟨92444547800070821210925853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123259397066761094947901137 92444547800070821210925853)
    ·
      refine ⟨34666705425026557954097195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92444547800070821210925853 34666705425026557954097195)
      ·
        refine ⟨52000058137539836931145793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34666705425026557954097195 52000058137539836931145793)
        ·
          refine ⟨39000043603154877698359345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52000058137539836931145793 39000043603154877698359345)
          ·
            refine ⟨29250032702366158273769509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39000043603154877698359345 29250032702366158273769509)
            ·
              refine ⟨5484381131693654676331783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29250032702366158273769509 5484381131693654676331783)
              ·
                refine ⟨8226571697540482014497675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484381131693654676331783 8226571697540482014497675)
                ·
                  refine ⟨12339857546310723021746513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8226571697540482014497675 12339857546310723021746513)
                  ·
                    refine ⟨9254893159733042266309885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12339857546310723021746513 9254893159733042266309885)
                    ·
                      refine ⟨3470584934899890849866207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9254893159733042266309885 3470584934899890849866207)
                      ·
                        rfl

theorem cell23_6758940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_6758940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758940 prefixEnd_6758940 := by exact prefixLift 6758940
  have htrace : WordTrace (prefixWord ++ tailWord_6758940) baseStart_6758940 baseEnd_6758940 := by
    simpa [prefixWord, tailWord_6758940, baseEnd_6758940] using wordTrace_append hprefix tailTrace_6758940
  have hstable : (prefixWord ++ tailWord_6758940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758940).length < 2 ^ (prefixWord ++ tailWord_6758940).sum := by decide
  have hdescent : baseEnd_6758940 < baseStart_6758940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758957 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6758957 : Nat := 118140960795 + 6758957 * 2 ^ 59
def prefixEnd_6758957 : Nat := 4983230072969 + 3 ^ 40 * 6758957 * 2
def baseEnd_6758957 : Nat := 3470593664071017283353629

theorem tailTrace_6758957 : CollatzResearch.WordTrace tailWord_6758957 prefixEnd_6758957 3470593664071017283353629 := by
  unfold tailWord_6758957
  simp only [CollatzResearch.WordTrace]
  refine ⟨246519414174460601799171125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164346276116307067866114083 246519414174460601799171125)
  ·
    refine ⟨23111195078855681418672293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246519414174460601799171125 23111195078855681418672293)
    ·
      refine ⟨4333349077285440266001055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23111195078855681418672293 4333349077285440266001055)
      ·
        refine ⟨6500023615928160399001583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4333349077285440266001055 6500023615928160399001583)
        ·
          refine ⟨9750035423892240598502375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6500023615928160399001583 9750035423892240598502375)
          ·
            refine ⟨14625053135838360897753563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9750035423892240598502375 14625053135838360897753563)
            ·
              refine ⟨21937579703757541346630345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14625053135838360897753563 21937579703757541346630345)
              ·
                refine ⟨16453184777818156009972759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21937579703757541346630345 16453184777818156009972759)
                ·
                  refine ⟨24679777166727234014959139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16453184777818156009972759 24679777166727234014959139)
                  ·
                    refine ⟨37019665750090851022438709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24679777166727234014959139 37019665750090851022438709)
                    ·
                      refine ⟨3470593664071017283353629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37019665750090851022438709 3470593664071017283353629)
                      ·
                        rfl

theorem cell23_6758957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6758957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758957 prefixEnd_6758957 := by exact prefixLift 6758957
  have htrace : WordTrace (prefixWord ++ tailWord_6758957) baseStart_6758957 baseEnd_6758957 := by
    simpa [prefixWord, tailWord_6758957, baseEnd_6758957] using wordTrace_append hprefix tailTrace_6758957
  have hstable : (prefixWord ++ tailWord_6758957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758957).length < 2 ^ (prefixWord ++ tailWord_6758957).sum := by decide
  have hdescent : baseEnd_6758957 < baseStart_6758957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758964 : List Nat := [2, 5, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_6758964 : Nat := 118140960795 + 6758964 * 2 ^ 59
def prefixEnd_6758964 : Nat := 4983230072969 + 3 ^ 40 * 6758964 * 2
def baseEnd_6758964 : Nat := 1156865752811866251988699

theorem tailTrace_6758964 : CollatzResearch.WordTrace tailWord_6758964 prefixEnd_6758964 1156865752811866251988699 := by
  unfold tailWord_6758964
  simp only [CollatzResearch.WordTrace]
  refine ⟨123259834742717620997337973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164346446323623494663117297 123259834742717620997337973)
  ·
    refine ⟨11555609507129776968500435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123259834742717620997337973 11555609507129776968500435)
    ·
      refine ⟨17333414260694665452750653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11555609507129776968500435 17333414260694665452750653)
      ·
        refine ⟨6500030347760499544781495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17333414260694665452750653 6500030347760499544781495)
        ·
          refine ⟨9750045521640749317172243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6500030347760499544781495 9750045521640749317172243)
          ·
            refine ⟨14625068282461123975758365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9750045521640749317172243 14625068282461123975758365)
            ·
              refine ⟨5484400605922921490909387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14625068282461123975758365 5484400605922921490909387)
              ·
                refine ⟨8226600908884382236364081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484400605922921490909387 8226600908884382236364081)
                ·
                  refine ⟨6169950681663286677273061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8226600908884382236364081 6169950681663286677273061)
                  ·
                    refine ⟨1156865752811866251988699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6169950681663286677273061 1156865752811866251988699)
                    ·
                      rfl

theorem cell23_6758964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_6758964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758964 prefixEnd_6758964 := by exact prefixLift 6758964
  have htrace : WordTrace (prefixWord ++ tailWord_6758964) baseStart_6758964 baseEnd_6758964 := by
    simpa [prefixWord, tailWord_6758964, baseEnd_6758964] using wordTrace_append hprefix tailTrace_6758964
  have hstable : (prefixWord ++ tailWord_6758964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758964).length < 2 ^ (prefixWord ++ tailWord_6758964).sum := by decide
  have hdescent : baseEnd_6758964 < baseStart_6758964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758979 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 5]
def baseStart_6758979 : Nat := 118140960795 + 6758979 * 2 ^ 59
def prefixEnd_6758979 : Nat := 4983230072969 + 3 ^ 40 * 6758979 * 2
def baseEnd_6758979 : Nat := 3470604960645416197278527

theorem tailTrace_6758979 : CollatzResearch.WordTrace tailWord_6758979 prefixEnd_6758979 3470604960645416197278527 := by
  unfold tailWord_6758979
  simp only [CollatzResearch.WordTrace]
  refine ⟨246520216580380899556471991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164346811053587266370981327 246520216580380899556471991)
  ·
    refine ⟨369780324870571349334707987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246520216580380899556471991 369780324870571349334707987)
    ·
      refine ⟨554670487305857024002061981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369780324870571349334707987 554670487305857024002061981)
      ·
        refine ⟨208001432739696384000773243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 554670487305857024002061981 208001432739696384000773243)
        ·
          refine ⟨312002149109544576001159865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208001432739696384000773243 312002149109544576001159865)
          ·
            refine ⟨234001611832158432000869899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312002149109544576001159865 234001611832158432000869899)
            ·
              refine ⟨351002417748237648001304849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234001611832158432000869899 351002417748237648001304849)
              ·
                refine ⟨263251813311178236000978637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351002417748237648001304849 263251813311178236000978637)
                ·
                  refine ⟨98719429991691838500366989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263251813311178236000978637 98719429991691838500366989)
                  ·
                    refine ⟨37019786246884439437637621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98719429991691838500366989 37019786246884439437637621)
                    ·
                      refine ⟨3470604960645416197278527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37019786246884439437637621 3470604960645416197278527)
                      ·
                        rfl

theorem cell23_6758979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_6758979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758979 prefixEnd_6758979 := by exact prefixLift 6758979
  have htrace : WordTrace (prefixWord ++ tailWord_6758979) baseStart_6758979 baseEnd_6758979 := by
    simpa [prefixWord, tailWord_6758979, baseEnd_6758979] using wordTrace_append hprefix tailTrace_6758979
  have hstable : (prefixWord ++ tailWord_6758979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758979).length < 2 ^ (prefixWord ++ tailWord_6758979).sum := by decide
  have hdescent : baseEnd_6758979 < baseStart_6758979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6758996 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_6758996 : Nat := 118140960795 + 6758996 * 2 ^ 59
def prefixEnd_6758996 : Nat := 4983230072969 + 3 ^ 40 * 6758996 * 2
def baseEnd_6758996 : Nat := 3470613689816542630765949

theorem tailTrace_6758996 : CollatzResearch.WordTrace tailWord_6758996 prefixEnd_6758996 3470613689816542630765949 := by
  unfold tailWord_6758996
  simp only [CollatzResearch.WordTrace]
  refine ⟨123260418310659655729920421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164347224414212874306560561 123260418310659655729920421)
  ·
    refine ⟨23111328433248685449360079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123260418310659655729920421 23111328433248685449360079)
    ·
      refine ⟨34666992649873028174040119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23111328433248685449360079 34666992649873028174040119)
      ·
        refine ⟨52000488974809542261060179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34666992649873028174040119 52000488974809542261060179)
        ·
          refine ⟨78000733462214313391590269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52000488974809542261060179 78000733462214313391590269)
          ·
            refine ⟨29250275048330367521846351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78000733462214313391590269 29250275048330367521846351)
            ·
              refine ⟨43875412572495551282769527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29250275048330367521846351 43875412572495551282769527)
              ·
                refine ⟨65813118858743326924154291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43875412572495551282769527 65813118858743326924154291)
                ·
                  refine ⟨98719678288114990386231437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65813118858743326924154291 98719678288114990386231437)
                  ·
                    refine ⟨37019879358043121394836789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98719678288114990386231437 37019879358043121394836789)
                    ·
                      refine ⟨3470613689816542630765949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37019879358043121394836789 3470613689816542630765949)
                      ·
                        rfl

theorem cell23_6758996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_6758996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6758996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6758996 prefixEnd_6758996 := by exact prefixLift 6758996
  have htrace : WordTrace (prefixWord ++ tailWord_6758996) baseStart_6758996 baseEnd_6758996 := by
    simpa [prefixWord, tailWord_6758996, baseEnd_6758996] using wordTrace_append hprefix tailTrace_6758996
  have hstable : (prefixWord ++ tailWord_6758996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6758996).length < 2 ^ (prefixWord ++ tailWord_6758996).sum := by decide
  have hdescent : baseEnd_6758996 < baseStart_6758996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6758996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759019 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 8]
def baseStart_6759019 : Nat := 118140960795 + 6759019 * 2 ^ 59
def prefixEnd_6759019 : Nat := 4983230072969 + 3 ^ 40 * 6759019 * 2
def baseEnd_6759019 : Nat := 3470625499871596040778343

theorem tailTrace_6759019 : CollatzResearch.WordTrace tailWord_6759019 prefixEnd_6759019 3470625499871596040778343 := by
  unfold tailWord_6759019
  simp only [CollatzResearch.WordTrace]
  refine ⟨246521675500235986387928111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164347783666823990925285407 246521675500235986387928111)
  ·
    refine ⟨369782513250353979581892167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246521675500235986387928111 369782513250353979581892167)
    ·
      refine ⟨554673769875530969372838251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369782513250353979581892167 554673769875530969372838251)
      ·
        refine ⟨832010654813296454059257377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554673769875530969372838251 832010654813296454059257377)
        ·
          refine ⟨624007991109972340544443033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832010654813296454059257377 624007991109972340544443033)
          ·
            refine ⟨468005993332479255408332275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624007991109972340544443033 468005993332479255408332275)
            ·
              refine ⟨702008989998718883112498413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468005993332479255408332275 702008989998718883112498413)
              ·
                refine ⟨263253371249519581167186905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 702008989998718883112498413 263253371249519581167186905)
                ·
                  refine ⟨197440028437139685875390179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263253371249519581167186905 197440028437139685875390179)
                  ·
                    refine ⟨296160042655709528813085269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 197440028437139685875390179 296160042655709528813085269)
                    ·
                      refine ⟨3470625499871596040778343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 296160042655709528813085269 3470625499871596040778343)
                      ·
                        rfl

theorem cell23_6759019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_6759019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759019 prefixEnd_6759019 := by exact prefixLift 6759019
  have htrace : WordTrace (prefixWord ++ tailWord_6759019) baseStart_6759019 baseEnd_6759019 := by
    simpa [prefixWord, tailWord_6759019, baseEnd_6759019] using wordTrace_append hprefix tailTrace_6759019
  have hstable : (prefixWord ++ tailWord_6759019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759019).length < 2 ^ (prefixWord ++ tailWord_6759019).sum := by decide
  have hdescent : baseEnd_6759019 < baseStart_6759019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759070 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_6759070 : Nat := 118140960795 + 6759070 * 2 ^ 59
def prefixEnd_6759070 : Nat := 4983230072969 + 3 ^ 40 * 6759070 * 2
def baseEnd_6759070 : Nat := 3470651687384975341240609

theorem tailTrace_6759070 : CollatzResearch.WordTrace tailWord_6759070 prefixEnd_6759070 3470651687384975341240609 := by
  unfold tailWord_6759070
  simp only [CollatzResearch.WordTrace]
  refine ⟨30815441952881402762254333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164349023748700814732023109 30815441952881402762254333)
  ·
    refine ⟨11555790732330526035845375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30815441952881402762254333 11555790732330526035845375)
    ·
      refine ⟨17333686098495789053768063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11555790732330526035845375 17333686098495789053768063)
      ·
        refine ⟨26000529147743683580652095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17333686098495789053768063 26000529147743683580652095)
        ·
          refine ⟨39000793721615525370978143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26000529147743683580652095 39000793721615525370978143)
          ·
            refine ⟨58501190582423288056467215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39000793721615525370978143 58501190582423288056467215)
            ·
              refine ⟨87751785873634932084700823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58501190582423288056467215 87751785873634932084700823)
              ·
                refine ⟨131627678810452398127051235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87751785873634932084700823 131627678810452398127051235)
                ·
                  refine ⟨197441518215678597190576853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131627678810452398127051235 197441518215678597190576853)
                  ·
                    refine ⟨4627535583179967121654145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 197441518215678597190576853 4627535583179967121654145)
                    ·
                      refine ⟨3470651687384975341240609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627535583179967121654145 3470651687384975341240609)
                      ·
                        rfl

theorem cell23_6759070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_6759070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759070 prefixEnd_6759070 := by exact prefixLift 6759070
  have htrace : WordTrace (prefixWord ++ tailWord_6759070) baseStart_6759070 baseEnd_6759070 := by
    simpa [prefixWord, tailWord_6759070, baseEnd_6759070] using wordTrace_append hprefix tailTrace_6759070
  have hstable : (prefixWord ++ tailWord_6759070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759070).length < 2 ^ (prefixWord ++ tailWord_6759070).sum := by decide
  have hdescent : baseEnd_6759070 < baseStart_6759070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759103 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 3]
def baseStart_6759103 : Nat := 118140960795 + 6759103 * 2 ^ 59
def prefixEnd_6759103 : Nat := 4983230072969 + 3 ^ 40 * 6759103 * 2
def baseEnd_6759103 : Nat := 3470668632246573712127957

theorem tailTrace_6759103 : CollatzResearch.WordTrace tailWord_6759103 prefixEnd_6759103 3470668632246573712127957 := by
  unfold tailWord_6759103
  simp only [CollatzResearch.WordTrace]
  refine ⟨246524739231931668733985963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164349826154621112489323975 246524739231931668733985963)
  ·
    refine ⟨369787108847897503100978945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246524739231931668733985963 369787108847897503100978945)
    ·
      refine ⟨277340331635923127325734209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369787108847897503100978945 277340331635923127325734209)
      ·
        refine ⟨208005248726942345494300657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277340331635923127325734209 208005248726942345494300657)
        ·
          refine ⟨156003936545206759120725493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208005248726942345494300657 156003936545206759120725493)
          ·
            refine ⟨14625369051113133667568015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156003936545206759120725493 14625369051113133667568015)
            ·
              refine ⟨21938053576669700501352023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14625369051113133667568015 21938053576669700501352023)
              ·
                refine ⟨32907080365004550752028035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21938053576669700501352023 32907080365004550752028035)
                ·
                  refine ⟨49360620547506826128042053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32907080365004550752028035 49360620547506826128042053)
                  ·
                    refine ⟨9255116352657529899007885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49360620547506826128042053 9255116352657529899007885)
                    ·
                      refine ⟨3470668632246573712127957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9255116352657529899007885 3470668632246573712127957)
                      ·
                        rfl

theorem cell23_6759103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_6759103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759103 prefixEnd_6759103 := by exact prefixLift 6759103
  have htrace : WordTrace (prefixWord ++ tailWord_6759103) baseStart_6759103 baseEnd_6759103 := by
    simpa [prefixWord, tailWord_6759103, baseEnd_6759103] using wordTrace_append hprefix tailTrace_6759103
  have hstable : (prefixWord ++ tailWord_6759103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759103).length < 2 ^ (prefixWord ++ tailWord_6759103).sum := by decide
  have hdescent : baseEnd_6759103 < baseStart_6759103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759140 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 6]
def baseStart_6759140 : Nat := 118140960795 + 6759140 * 2 ^ 59
def prefixEnd_6759140 : Nat := 4983230072969 + 3 ^ 40 * 6759140 * 2
def baseEnd_6759140 : Nat := 385631959003421118596143

theorem tailTrace_6759140 : CollatzResearch.WordTrace tailWord_6759140 prefixEnd_6759140 385631959003421118596143 := by
  unfold tailWord_6759140
  simp only [CollatzResearch.WordTrace]
  refine ⟨123263044366398812026541437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164350725821865082702055249 123263044366398812026541437)
  ·
    refine ⟨46223641637399554509953039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123263044366398812026541437 46223641637399554509953039)
    ·
      refine ⟨69335462456099331764929559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46223641637399554509953039 69335462456099331764929559)
      ·
        refine ⟨104003193684148997647394339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69335462456099331764929559 104003193684148997647394339)
        ·
          refine ⟨156004790526223496471091509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104003193684148997647394339 156004790526223496471091509)
          ·
            refine ⟨14625449111833452794164829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156004790526223496471091509 14625449111833452794164829)
            ·
              refine ⟨5484543416937544797811811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14625449111833452794164829 5484543416937544797811811)
              ·
                refine ⟨8226815125406317196717717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484543416937544797811811 8226815125406317196717717)
                ·
                  refine ⟨385631959003421118596143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8226815125406317196717717 385631959003421118596143)
                  ·
                    rfl

theorem cell23_6759140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_6759140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759140 prefixEnd_6759140 := by exact prefixLift 6759140
  have htrace : WordTrace (prefixWord ++ tailWord_6759140) baseStart_6759140 baseEnd_6759140 := by
    simpa [prefixWord, tailWord_6759140, baseEnd_6759140] using wordTrace_append hprefix tailTrace_6759140
  have hstable : (prefixWord ++ tailWord_6759140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759140).length < 2 ^ (prefixWord ++ tailWord_6759140).sum := by decide
  have hdescent : baseEnd_6759140 < baseStart_6759140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759160 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 2, 3, 2]
def baseStart_6759160 : Nat := 118140960795 + 6759160 * 2 ^ 59
def prefixEnd_6759160 : Nat := 4983230072969 + 3 ^ 40 * 6759160 * 2
def baseEnd_6759160 : Nat := 3470697900643879989115195

theorem tailTrace_6759160 : CollatzResearch.WordTrace tailWord_6759160 prefixEnd_6759160 3470697900643879989115195 := by
  unfold tailWord_6759160
  simp only [CollatzResearch.WordTrace]
  refine ⟨123263409096362583734405467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164351212128483444979207289 123263409096362583734405467)
  ·
    refine ⟨184895113644543875601608201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123263409096362583734405467 184895113644543875601608201)
    ·
      refine ⟨138671335233407906701206151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184895113644543875601608201 138671335233407906701206151)
      ·
        refine ⟨208007002850111860051809227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138671335233407906701206151 208007002850111860051809227)
        ·
          refine ⟨312010504275167790077713841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208007002850111860051809227 312010504275167790077713841)
          ·
            refine ⟨234007878206375842558285381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312010504275167790077713841 234007878206375842558285381)
            ·
              refine ⟨43876477163695470479678509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234007878206375842558285381 43876477163695470479678509)
              ·
                refine ⟨16453678936385801429879441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43876477163695470479678509 16453678936385801429879441)
                ·
                  refine ⟨12340259202289351072409581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16453678936385801429879441 12340259202289351072409581)
                  ·
                    refine ⟨4627597200858506652153593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12340259202289351072409581 4627597200858506652153593)
                    ·
                      refine ⟨3470697900643879989115195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627597200858506652153593 3470697900643879989115195)
                      ·
                        rfl

theorem cell23_6759160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_6759160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759160 prefixEnd_6759160 := by exact prefixLift 6759160
  have htrace : WordTrace (prefixWord ++ tailWord_6759160) baseStart_6759160 baseEnd_6759160 := by
    simpa [prefixWord, tailWord_6759160, baseEnd_6759160] using wordTrace_append hprefix tailTrace_6759160
  have hstable : (prefixWord ++ tailWord_6759160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759160).length < 2 ^ (prefixWord ++ tailWord_6759160).sum := by decide
  have hdescent : baseEnd_6759160 < baseStart_6759160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759183 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 4, 4]
def baseStart_6759183 : Nat := 118140960795 + 6759183 * 2 ^ 59
def prefixEnd_6759183 : Nat := 4983230072969 + 3 ^ 40 * 6759183 * 2
def baseEnd_6759183 : Nat := 1156903236899644466375863

theorem tailTrace_6759183 : CollatzResearch.WordTrace tailWord_6759183 prefixEnd_6759183 1156903236899644466375863 := by
  unfold tailWord_6759183
  simp only [CollatzResearch.WordTrace]
  refine ⟨246527657071641842396898203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164351771381094561597932135 246527657071641842396898203)
  ·
    refine ⟨369791485607462763595347305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246527657071641842396898203 369791485607462763595347305)
    ·
      refine ⟨277343614205597072696510479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369791485607462763595347305 277343614205597072696510479)
      ·
        refine ⟨416015421308395609044765719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277343614205597072696510479 416015421308395609044765719)
        ·
          refine ⟨624023131962593413567148579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416015421308395609044765719 624023131962593413567148579)
          ·
            refine ⟨936034697943890120350722869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624023131962593413567148579 936034697943890120350722869)
            ·
              refine ⟨87753252932239698782880269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 936034697943890120350722869 87753252932239698782880269)
              ·
                refine ⟨32907469849589887043580101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87753252932239698782880269 32907469849589887043580101)
                ·
                  refine ⟨6170150596798103820671269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32907469849589887043580101 6170150596798103820671269)
                  ·
                    refine ⟨1156903236899644466375863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6170150596798103820671269 1156903236899644466375863)
                    ·
                      rfl

theorem cell23_6759183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 4].length) (baseStart_6759183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759183 prefixEnd_6759183 := by exact prefixLift 6759183
  have htrace : WordTrace (prefixWord ++ tailWord_6759183) baseStart_6759183 baseEnd_6759183 := by
    simpa [prefixWord, tailWord_6759183, baseEnd_6759183] using wordTrace_append hprefix tailTrace_6759183
  have hstable : (prefixWord ++ tailWord_6759183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759183).length < 2 ^ (prefixWord ++ tailWord_6759183).sum := by decide
  have hdescent : baseEnd_6759183 < baseStart_6759183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759203 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 4]
def baseStart_6759203 : Nat := 118140960795 + 6759203 * 2 ^ 59
def prefixEnd_6759203 : Nat := 4983230072969 + 3 ^ 40 * 6759203 * 2
def baseEnd_6759203 : Nat := 3470719980312023320877497

theorem tailTrace_6759203 : CollatzResearch.WordTrace tailWord_6759203 prefixEnd_6759203 3470719980312023320877497 := by
  unfold tailWord_6759203
  simp only [CollatzResearch.WordTrace]
  refine ⟨246528386531569385812626263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164352257687712923875084175 246528386531569385812626263)
  ·
    refine ⟨369792579797354078718939395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246528386531569385812626263 369792579797354078718939395)
    ·
      refine ⟨554688869696031118078409093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369792579797354078718939395 554688869696031118078409093)
      ·
        refine ⟨104004163068005834639701705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 554688869696031118078409093 104004163068005834639701705)
        ·
          refine ⟨78003122301004375979776279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104004163068005834639701705 78003122301004375979776279)
          ·
            refine ⟨117004683451506563969664419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78003122301004375979776279 117004683451506563969664419)
            ·
              refine ⟨175507025177259845954496629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117004683451506563969664419 175507025177259845954496629)
              ·
                refine ⟨16453783610368110558234059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175507025177259845954496629 16453783610368110558234059)
                ·
                  refine ⟨24680675415552165837351089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16453783610368110558234059 24680675415552165837351089)
                  ·
                    refine ⟨18510506561664124378013317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24680675415552165837351089 18510506561664124378013317)
                    ·
                      refine ⟨3470719980312023320877497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18510506561664124378013317 3470719980312023320877497)
                      ·
                        rfl

theorem cell23_6759203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_6759203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759203 prefixEnd_6759203 := by exact prefixLift 6759203
  have htrace : WordTrace (prefixWord ++ tailWord_6759203) baseStart_6759203 baseEnd_6759203 := by
    simpa [prefixWord, tailWord_6759203, baseEnd_6759203] using wordTrace_append hprefix tailTrace_6759203
  have hstable : (prefixWord ++ tailWord_6759203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759203).length < 2 ^ (prefixWord ++ tailWord_6759203).sum := by decide
  have hdescent : baseEnd_6759203 < baseStart_6759203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759204 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_6759204 : Nat := 118140960795 + 6759204 * 2 ^ 59
def prefixEnd_6759204 : Nat := 4983230072969 + 3 ^ 40 * 6759204 * 2
def baseEnd_6759204 : Nat := 1156906831264225938988331

theorem tailTrace_6759204 : CollatzResearch.WordTrace tailWord_6759204 prefixEnd_6759204 1156906831264225938988331 := by
  unfold tailWord_6759204
  simp only [CollatzResearch.WordTrace]
  refine ⟨123264211502282881491706333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164352282003043841988941777 123264211502282881491706333)
  ·
    refine ⟨46224079313356080559389875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123264211502282881491706333 46224079313356080559389875)
    ·
      refine ⟨69336118970034120839084813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46224079313356080559389875 69336118970034120839084813)
      ·
        refine ⟨26001044613762795314656805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69336118970034120839084813 26001044613762795314656805)
        ·
          refine ⟨4875195865080524121498151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26001044613762795314656805 4875195865080524121498151)
          ·
            refine ⟨7312793797620786182247227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4875195865080524121498151 7312793797620786182247227)
            ·
              refine ⟨10969190696431179273370841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312793797620786182247227 10969190696431179273370841)
              ·
                refine ⟨8226893022323384455028131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10969190696431179273370841 8226893022323384455028131)
                ·
                  refine ⟨12340339533485076682542197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8226893022323384455028131 12340339533485076682542197)
                  ·
                    refine ⟨1156906831264225938988331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12340339533485076682542197 1156906831264225938988331)
                    ·
                      rfl

theorem cell23_6759204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_6759204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759204 prefixEnd_6759204 := by exact prefixLift 6759204
  have htrace : WordTrace (prefixWord ++ tailWord_6759204) baseStart_6759204 baseEnd_6759204 := by
    simpa [prefixWord, tailWord_6759204, baseEnd_6759204] using wordTrace_append hprefix tailTrace_6759204
  have hstable : (prefixWord ++ tailWord_6759204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759204).length < 2 ^ (prefixWord ++ tailWord_6759204).sum := by decide
  have hdescent : baseEnd_6759204 < baseStart_6759204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759224 : List Nat := [2, 1, 2, 1, 3, 2, 2, 5, 1, 2, 2]
def baseStart_6759224 : Nat := 118140960795 + 6759224 * 2 ^ 59
def prefixEnd_6759224 : Nat := 4983230072969 + 3 ^ 40 * 6759224 * 2
def baseEnd_6759224 : Nat := 3470730763405767738714901

theorem tailTrace_6759224 : CollatzResearch.WordTrace tailWord_6759224 prefixEnd_6759224 3470730763405767738714901 := by
  unfold tailWord_6759224
  simp only [CollatzResearch.WordTrace]
  refine ⟨123264576232246653199570363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164352768309662204266093817 123264576232246653199570363)
  ·
    refine ⟨184896864348369979799355545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123264576232246653199570363 184896864348369979799355545)
    ·
      refine ⟨138672648261277484849516659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184896864348369979799355545 138672648261277484849516659)
      ·
        refine ⟨208008972391916227274274989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138672648261277484849516659 208008972391916227274274989)
        ·
          refine ⟨78003364646968585227853121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208008972391916227274274989 78003364646968585227853121)
          ·
            refine ⟨58502523485226438920889841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78003364646968585227853121 58502523485226438920889841)
            ·
              refine ⟨43876892613919829190667381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58502523485226438920889841 43876892613919829190667381)
              ·
                refine ⟨4113458682554983986625067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43876892613919829190667381 4113458682554983986625067)
                ·
                  refine ⟨6170188023832475979937601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113458682554983986625067 6170188023832475979937601)
                  ·
                    refine ⟨4627641017874356984953201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6170188023832475979937601 4627641017874356984953201)
                    ·
                      refine ⟨3470730763405767738714901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627641017874356984953201 3470730763405767738714901)
                      ·
                        rfl

theorem cell23_6759224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 2, 2].length) (baseStart_6759224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759224 prefixEnd_6759224 := by exact prefixLift 6759224
  have htrace : WordTrace (prefixWord ++ tailWord_6759224) baseStart_6759224 baseEnd_6759224 := by
    simpa [prefixWord, tailWord_6759224, baseEnd_6759224] using wordTrace_append hprefix tailTrace_6759224
  have hstable : (prefixWord ++ tailWord_6759224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759224).length < 2 ^ (prefixWord ++ tailWord_6759224).sum := by decide
  have hdescent : baseEnd_6759224 < baseStart_6759224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759230 : List Nat := [4, 2, 1, 2, 4, 10]
def baseStart_6759230 : Nat := 118140960795 + 6759230 * 2 ^ 59
def prefixEnd_6759230 : Nat := 4983230072969 + 3 ^ 40 * 6759230 * 2
def baseEnd_6759230 : Nat := 14282855326295039980411

theorem tailTrace_6759230 : CollatzResearch.WordTrace tailWord_6759230 prefixEnd_6759230 14282855326295039980411 := by
  unfold tailWord_6759230
  simp only [CollatzResearch.WordTrace]
  refine ⟨30816171412808946177982393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164352914201647712949239429 30816171412808946177982393)
  ·
    refine ⟨23112128559606709633486795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30816171412808946177982393 23112128559606709633486795)
    ·
      refine ⟨34668192839410064450230193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23112128559606709633486795 34668192839410064450230193)
      ·
        refine ⟨26001144629557548337672645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34668192839410064450230193 26001144629557548337672645)
        ·
          refine ⟨4875214618042040313313621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26001144629557548337672645 4875214618042040313313621)
          ·
            refine ⟨14282855326295039980411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4875214618042040313313621 14282855326295039980411)
            ·
              rfl

theorem cell23_6759230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 10].length) (baseStart_6759230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759230 prefixEnd_6759230 := by exact prefixLift 6759230
  have htrace : WordTrace (prefixWord ++ tailWord_6759230) baseStart_6759230 baseEnd_6759230 := by
    simpa [prefixWord, tailWord_6759230, baseEnd_6759230] using wordTrace_append hprefix tailTrace_6759230
  have hstable : (prefixWord ++ tailWord_6759230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759230).length < 2 ^ (prefixWord ++ tailWord_6759230).sum := by decide
  have hdescent : baseEnd_6759230 < baseStart_6759230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759241 : List Nat := [1, 2, 1, 1, 2, 5, 4, 2, 1, 2, 2]
def baseStart_6759241 : Nat := 118140960795 + 6759241 * 2 ^ 59
def prefixEnd_6759241 : Nat := 4983230072969 + 3 ^ 40 * 6759241 * 2
def baseEnd_6759241 : Nat := 3470739492576894172202323

theorem tailTrace_6759241 : CollatzResearch.WordTrace tailWord_6759241 prefixEnd_6759241 3470739492576894172202323 := by
  unfold tailWord_6759241
  simp only [CollatzResearch.WordTrace]
  refine ⟨246529772505431718302509577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164353181670287812201673051 246529772505431718302509577)
  ·
    refine ⟨184897329379073788726882183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246529772505431718302509577 184897329379073788726882183)
    ·
      refine ⟨277345994068610683090323275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184897329379073788726882183 277345994068610683090323275)
      ·
        refine ⟨416018991102916024635484913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277345994068610683090323275 416018991102916024635484913)
        ·
          refine ⟨312014243327187018476613685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416018991102916024635484913 312014243327187018476613685)
          ·
            refine ⟨29251335311923782982182533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 312014243327187018476613685 29251335311923782982182533)
            ·
              refine ⟨5484625370985709309159225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29251335311923782982182533 5484625370985709309159225)
              ·
                refine ⟨4113469028239281981869419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5484625370985709309159225 4113469028239281981869419)
                ·
                  refine ⟨6170203542358922972804129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113469028239281981869419 6170203542358922972804129)
                  ·
                    refine ⟨4627652656769192229603097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6170203542358922972804129 4627652656769192229603097)
                    ·
                      refine ⟨3470739492576894172202323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627652656769192229603097 3470739492576894172202323)
                      ·
                        rfl

theorem cell23_6759241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 2, 2].length) (baseStart_6759241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759241 prefixEnd_6759241 := by exact prefixLift 6759241
  have htrace : WordTrace (prefixWord ++ tailWord_6759241) baseStart_6759241 baseEnd_6759241 := by
    simpa [prefixWord, tailWord_6759241, baseEnd_6759241] using wordTrace_append hprefix tailTrace_6759241
  have hstable : (prefixWord ++ tailWord_6759241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759241).length < 2 ^ (prefixWord ++ tailWord_6759241).sum := by decide
  have hdescent : baseEnd_6759241 < baseStart_6759241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759257 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 3]
def baseStart_6759257 : Nat := 118140960795 + 6759257 * 2 ^ 59
def prefixEnd_6759257 : Nat := 4983230072969 + 3 ^ 40 * 6759257 * 2
def baseEnd_6759257 : Nat := 3470747708267366109602249

theorem tailTrace_6759257 : CollatzResearch.WordTrace tailWord_6759257 prefixEnd_6759257 3470747708267366109602249 := by
  unfold tailWord_6759257
  simp only [CollatzResearch.WordTrace]
  refine ⟨246530356073373753035092025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164353570715582502023394683 246530356073373753035092025)
  ·
    refine ⟨184897767055030314776319019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246530356073373753035092025 184897767055030314776319019)
    ·
      refine ⟨277346650582545472164478529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184897767055030314776319019 277346650582545472164478529)
      ·
        refine ⟨208009987936909104123358897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277346650582545472164478529 208009987936909104123358897)
        ·
          refine ⟨156007490952681828092519173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208009987936909104123358897 156007490952681828092519173)
          ·
            refine ⟨29251404553627842767347345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156007490952681828092519173 29251404553627842767347345)
            ·
              refine ⟨21938553415220882075510509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29251404553627842767347345 21938553415220882075510509)
              ·
                refine ⟨8226957530707830778316441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21938553415220882075510509 8226957530707830778316441)
                ·
                  refine ⟨6170218148030873083737331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8226957530707830778316441 6170218148030873083737331)
                  ·
                    refine ⟨9255327222046309625605997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6170218148030873083737331 9255327222046309625605997)
                    ·
                      refine ⟨3470747708267366109602249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9255327222046309625605997 3470747708267366109602249)
                      ·
                        rfl

theorem cell23_6759257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_6759257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759257 prefixEnd_6759257 := by exact prefixLift 6759257
  have htrace : WordTrace (prefixWord ++ tailWord_6759257) baseStart_6759257 baseEnd_6759257 := by
    simpa [prefixWord, tailWord_6759257, baseEnd_6759257] using wordTrace_append hprefix tailTrace_6759257
  have hstable : (prefixWord ++ tailWord_6759257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759257).length < 2 ^ (prefixWord ++ tailWord_6759257).sum := by decide
  have hdescent : baseEnd_6759257 < baseStart_6759257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759263 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_6759263 : Nat := 118140960795 + 6759263 * 2 ^ 59
def prefixEnd_6759263 : Nat := 4983230072969 + 3 ^ 40 * 6759263 * 2
def baseEnd_6759263 : Nat := 3470750789151293086127221

theorem tailTrace_6759263 : CollatzResearch.WordTrace tailWord_6759263 prefixEnd_6759263 3470750789151293086127221 := by
  unfold tailWord_6759263
  simp only [CollatzResearch.WordTrace]
  refine ⟨246530574911352016059810443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164353716607568010706540295 246530574911352016059810443)
  ·
    refine ⟨369795862367028024089715665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246530574911352016059810443 369795862367028024089715665)
    ·
      refine ⟨277346896775271018067286749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369795862367028024089715665 277346896775271018067286749)
      ·
        refine ⟨104005086290726631775232531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277346896775271018067286749 104005086290726631775232531)
        ·
          refine ⟨156007629436089947662848797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104005086290726631775232531 156007629436089947662848797)
          ·
            refine ⟨58502861038533730373568299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156007629436089947662848797 58502861038533730373568299)
            ·
              refine ⟨87754291557800595560352449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58502861038533730373568299 87754291557800595560352449)
              ·
                refine ⟨65815718668350446670264337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87754291557800595560352449 65815718668350446670264337)
                ·
                  refine ⟨49361789001262835002698253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65815718668350446670264337 49361789001262835002698253)
                  ·
                    refine ⟨18510670875473563126011845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49361789001262835002698253 18510670875473563126011845)
                    ·
                      refine ⟨3470750789151293086127221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18510670875473563126011845 3470750789151293086127221)
                      ·
                        rfl

theorem cell23_6759263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_6759263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759263 prefixEnd_6759263 := by exact prefixLift 6759263
  have htrace : WordTrace (prefixWord ++ tailWord_6759263) baseStart_6759263 baseEnd_6759263 := by
    simpa [prefixWord, tailWord_6759263, baseEnd_6759263] using wordTrace_append hprefix tailTrace_6759263
  have hstable : (prefixWord ++ tailWord_6759263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759263).length < 2 ^ (prefixWord ++ tailWord_6759263).sum := by decide
  have hdescent : baseEnd_6759263 < baseStart_6759263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759267 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 3, 3, 2]
def baseStart_6759267 : Nat := 118140960795 + 6759267 * 2 ^ 59
def prefixEnd_6759267 : Nat := 4983230072969 + 3 ^ 40 * 6759267 * 2
def baseEnd_6759267 : Nat := 3470752843073911070477203

theorem tailTrace_6759267 : CollatzResearch.WordTrace tailWord_6759267 prefixEnd_6759267 3470752843073911070477203 := by
  unfold tailWord_6759267
  simp only [CollatzResearch.WordTrace]
  refine ⟨246530720803337524742956055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164353813868891683161970703 246530720803337524742956055)
  ·
    refine ⟨369796081205006287114434083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246530720803337524742956055 369796081205006287114434083)
    ·
      refine ⟨554694121807509430671651125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369796081205006287114434083 554694121807509430671651125)
      ·
        refine ⟨52002573919454009125467293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 554694121807509430671651125 52002573919454009125467293)
        ·
          refine ⟨19500965219795253422050235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52002573919454009125467293 19500965219795253422050235)
          ·
            refine ⟨29251447829692880133075353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19500965219795253422050235 29251447829692880133075353)
            ·
              refine ⟨21938585872269660099806515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29251447829692880133075353 21938585872269660099806515)
              ·
                refine ⟨32907878808404490149709773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21938585872269660099806515 32907878808404490149709773)
                ·
                  refine ⟨12340454553151683806141165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32907878808404490149709773 12340454553151683806141165)
                  ·
                    refine ⟨4627670457431881427302937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12340454553151683806141165 4627670457431881427302937)
                    ·
                      refine ⟨3470752843073911070477203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627670457431881427302937 3470752843073911070477203)
                      ·
                        rfl

theorem cell23_6759267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_6759267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759267 prefixEnd_6759267 := by exact prefixLift 6759267
  have htrace : WordTrace (prefixWord ++ tailWord_6759267) baseStart_6759267 baseEnd_6759267 := by
    simpa [prefixWord, tailWord_6759267, baseEnd_6759267] using wordTrace_append hprefix tailTrace_6759267
  have hstable : (prefixWord ++ tailWord_6759267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759267).length < 2 ^ (prefixWord ++ tailWord_6759267).sum := by decide
  have hdescent : baseEnd_6759267 < baseStart_6759267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759278 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_6759278 : Nat := 118140960795 + 6759278 * 2 ^ 59
def prefixEnd_6759278 : Nat := 4983230072969 + 3 ^ 40 * 6759278 * 2
def baseEnd_6759278 : Nat := 3470758491361110527439653

theorem tailTrace_6759278 : CollatzResearch.WordTrace tailWord_6759278 prefixEnd_6759278 3470758491361110527439653 := by
  unfold tailWord_6759278
  simp only [CollatzResearch.WordTrace]
  refine ⟨30816390250787209202700811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164354081337531782414404325 30816390250787209202700811)
  ·
    refine ⟨46224585376180813804051217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30816390250787209202700811 46224585376180813804051217)
    ·
      refine ⟨34668439032135610353038413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46224585376180813804051217 34668439032135610353038413)
      ·
        refine ⟨13000664637050853882389405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34668439032135610353038413 13000664637050853882389405)
        ·
          refine ⟨4875249238894070205896027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13000664637050853882389405 4875249238894070205896027)
          ·
            refine ⟨7312873858341105308844041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4875249238894070205896027 7312873858341105308844041)
            ·
              refine ⟨5484655393755828981633031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7312873858341105308844041 5484655393755828981633031)
              ·
                refine ⟨8226983090633743472449547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484655393755828981633031 8226983090633743472449547)
                ·
                  refine ⟨12340474635950615208674321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8226983090633743472449547 12340474635950615208674321)
                  ·
                    refine ⟨9255355976962961406505741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12340474635950615208674321 9255355976962961406505741)
                    ·
                      refine ⟨3470758491361110527439653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9255355976962961406505741 3470758491361110527439653)
                      ·
                        rfl

theorem cell23_6759278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_6759278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759278 prefixEnd_6759278 := by exact prefixLift 6759278
  have htrace : WordTrace (prefixWord ++ tailWord_6759278) baseStart_6759278 baseEnd_6759278 := by
    simpa [prefixWord, tailWord_6759278, baseEnd_6759278] using wordTrace_append hprefix tailTrace_6759278
  have hstable : (prefixWord ++ tailWord_6759278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759278).length < 2 ^ (prefixWord ++ tailWord_6759278).sum := by decide
  have hdescent : baseEnd_6759278 < baseStart_6759278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759283 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 5]
def baseStart_6759283 : Nat := 118140960795 + 6759283 * 2 ^ 59
def prefixEnd_6759283 : Nat := 4983230072969 + 3 ^ 40 * 6759283 * 2
def baseEnd_6759283 : Nat := 3470761058764383007877129

theorem tailTrace_6759283 : CollatzResearch.WordTrace tailWord_6759283 prefixEnd_6759283 3470761058764383007877129 := by
  unfold tailWord_6759283
  simp only [CollatzResearch.WordTrace]
  refine ⟨246531304371279559475538503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164354202914186372983692335 246531304371279559475538503)
  ·
    refine ⟨369796956556919339213307755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246531304371279559475538503 369796956556919339213307755)
    ·
      refine ⟨554695434835379008819961633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369796956556919339213307755 554695434835379008819961633)
      ·
        refine ⟨416021576126534256614971225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554695434835379008819961633 416021576126534256614971225)
        ·
          refine ⟨312016182094900692461228419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416021576126534256614971225 312016182094900692461228419)
          ·
            refine ⟨468024273142351038691842629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312016182094900692461228419 468024273142351038691842629)
            ·
              refine ⟨87754551214190819754720493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 468024273142351038691842629 87754551214190819754720493)
              ·
                refine ⟨32907956705321557408020185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87754551214190819754720493 32907956705321557408020185)
                ·
                  refine ⟨24680967528991168056015139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32907956705321557408020185 24680967528991168056015139)
                  ·
                    refine ⟨37021451293486752084022709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24680967528991168056015139 37021451293486752084022709)
                    ·
                      refine ⟨3470761058764383007877129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37021451293486752084022709 3470761058764383007877129)
                      ·
                        rfl

theorem cell23_6759283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_6759283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759283 prefixEnd_6759283 := by exact prefixLift 6759283
  have htrace : WordTrace (prefixWord ++ tailWord_6759283) baseStart_6759283 baseEnd_6759283 := by
    simpa [prefixWord, tailWord_6759283, baseEnd_6759283] using wordTrace_append hprefix tailTrace_6759283
  have hstable : (prefixWord ++ tailWord_6759283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759283).length < 2 ^ (prefixWord ++ tailWord_6759283).sum := by decide
  have hdescent : baseEnd_6759283 < baseStart_6759283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759318 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6759318 : Nat := 118140960795 + 6759318 * 2 ^ 59
def prefixEnd_6759318 : Nat := 4983230072969 + 3 ^ 40 * 6759318 * 2
def baseEnd_6759318 : Nat := 3470779030587290370939469

theorem tailTrace_6759318 : CollatzResearch.WordTrace tailWord_6759318 prefixEnd_6759318 3470779030587290370939469 := by
  unfold tailWord_6759318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15408286307884547528316413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164355053950768506968708405 15408286307884547528316413)
  ·
    refine ⟨5778107365456705323118655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15408286307884547528316413 5778107365456705323118655)
    ·
      refine ⟨8667161048185057984677983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778107365456705323118655 8667161048185057984677983)
      ·
        refine ⟨13000741572277586977016975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667161048185057984677983 13000741572277586977016975)
        ·
          refine ⟨19501112358416380465525463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13000741572277586977016975 19501112358416380465525463)
          ·
            refine ⟨29251668537624570698288195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19501112358416380465525463 29251668537624570698288195)
            ·
              refine ⟨43877502806436856047432293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29251668537624570698288195 43877502806436856047432293)
              ·
                refine ⟨8227031776206910508893555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43877502806436856047432293 8227031776206910508893555)
                ·
                  refine ⟨12340547664310365763340333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8227031776206910508893555 12340547664310365763340333)
                  ·
                    refine ⟨4627705374116387161252625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12340547664310365763340333 4627705374116387161252625)
                    ·
                      refine ⟨3470779030587290370939469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627705374116387161252625 3470779030587290370939469)
                      ·
                        rfl

theorem cell23_6759318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6759318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759318 prefixEnd_6759318 := by exact prefixLift 6759318
  have htrace : WordTrace (prefixWord ++ tailWord_6759318) baseStart_6759318 baseEnd_6759318 := by
    simpa [prefixWord, tailWord_6759318, baseEnd_6759318] using wordTrace_append hprefix tailTrace_6759318
  have hstable : (prefixWord ++ tailWord_6759318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759318).length < 2 ^ (prefixWord ++ tailWord_6759318).sum := by decide
  have hdescent : baseEnd_6759318 < baseStart_6759318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759360 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 5]
def baseStart_6759360 : Nat := 118140960795 + 6759360 * 2 ^ 59
def prefixEnd_6759360 : Nat := 4983230072969 + 3 ^ 40 * 6759360 * 2
def baseEnd_6759360 : Nat := 3470800596774779206614275

theorem tailTrace_6759360 : CollatzResearch.WordTrace tailWord_6759360 prefixEnd_6759360 3470800596774779206614275 := by
  unfold tailWord_6759360
  simp only [CollatzResearch.WordTrace]
  refine ⟨123267056396000300813045767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164356075194667067750727689 123267056396000300813045767)
  ·
    refine ⟨184900584594000451219568651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123267056396000300813045767 184900584594000451219568651)
    ·
      refine ⟨277350876891000676829352977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184900584594000451219568651 277350876891000676829352977)
      ·
        refine ⟨208013157668250507622014733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277350876891000676829352977 208013157668250507622014733)
        ·
          refine ⟨78004934125593940358255525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208013157668250507622014733 78004934125593940358255525)
          ·
            refine ⟨14625925148548863817172911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78004934125593940358255525 14625925148548863817172911)
            ·
              refine ⟨21938887722823295725759367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14625925148548863817172911 21938887722823295725759367)
              ·
                refine ⟨32908331584234943588639051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21938887722823295725759367 32908331584234943588639051)
                ·
                  refine ⟨49362497376352415382958577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32908331584234943588639051 49362497376352415382958577)
                  ·
                    refine ⟨37021873032264311537218933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49362497376352415382958577 37021873032264311537218933)
                    ·
                      refine ⟨3470800596774779206614275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37021873032264311537218933 3470800596774779206614275)
                      ·
                        rfl

theorem cell23_6759360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_6759360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759360 prefixEnd_6759360 := by exact prefixLift 6759360
  have htrace : WordTrace (prefixWord ++ tailWord_6759360) baseStart_6759360 baseEnd_6759360 := by
    simpa [prefixWord, tailWord_6759360, baseEnd_6759360] using wordTrace_append hprefix tailTrace_6759360
  have hstable : (prefixWord ++ tailWord_6759360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759360).length < 2 ^ (prefixWord ++ tailWord_6759360).sum := by decide
  have hdescent : baseEnd_6759360 < baseStart_6759360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759370 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_6759370 : Nat := 118140960795 + 6759370 * 2 ^ 59
def prefixEnd_6759370 : Nat := 4983230072969 + 3 ^ 40 * 6759370 * 2
def baseEnd_6759370 : Nat := 3470805731581324167489229

theorem tailTrace_6759370 : CollatzResearch.WordTrace tailWord_6759370 prefixEnd_6759370 3470805731581324167489229 := by
  unfold tailWord_6759370
  simp only [CollatzResearch.WordTrace]
  refine ⟨61633619380491093333488891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164356318347976248889303709 61633619380491093333488891)
  ·
    refine ⟨92450429070736640000233337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61633619380491093333488891 92450429070736640000233337)
    ·
      refine ⟨69337821803052480000175003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92450429070736640000233337 69337821803052480000175003)
      ·
        refine ⟨104006732704578720000262505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69337821803052480000175003 104006732704578720000262505)
        ·
          refine ⟨78005049528434040000196879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104006732704578720000262505 78005049528434040000196879)
          ·
            refine ⟨117007574292651060000295319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78005049528434040000196879 117007574292651060000295319)
            ·
              refine ⟨175511361438976590000442979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117007574292651060000295319 175511361438976590000442979)
              ·
                refine ⟨263267042158464885000664469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175511361438976590000442979 263267042158464885000664469)
                ·
                  refine ⟨12340642601178041484406147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 263267042158464885000664469 12340642601178041484406147)
                  ·
                    refine ⟨18510963901767062226609221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12340642601178041484406147 18510963901767062226609221)
                    ·
                      refine ⟨3470805731581324167489229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18510963901767062226609221 3470805731581324167489229)
                      ·
                        rfl

theorem cell23_6759370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_6759370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759370 prefixEnd_6759370 := by exact prefixLift 6759370
  have htrace : WordTrace (prefixWord ++ tailWord_6759370) baseStart_6759370 baseEnd_6759370 := by
    simpa [prefixWord, tailWord_6759370, baseEnd_6759370] using wordTrace_append hprefix tailTrace_6759370
  have hstable : (prefixWord ++ tailWord_6759370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759370).length < 2 ^ (prefixWord ++ tailWord_6759370).sum := by decide
  have hdescent : baseEnd_6759370 < baseStart_6759370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759407 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 3]
def baseStart_6759407 : Nat := 118140960795 + 6759407 * 2 ^ 59
def prefixEnd_6759407 : Nat := 4983230072969 + 3 ^ 40 * 6759407 * 2
def baseEnd_6759407 : Nat := 3470824730365540522726559

theorem tailTrace_6759407 : CollatzResearch.WordTrace tailWord_6759407 prefixEnd_6759407 3470824730365540522726559 := by
  unfold tailWord_6759407
  simp only [CollatzResearch.WordTrace]
  refine ⟨246535827022830328653052475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164357218015220219102034983 246535827022830328653052475)
  ·
    refine ⟨369803740534245492979578713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246535827022830328653052475 369803740534245492979578713)
    ·
      refine ⟨277352805400684119734684035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369803740534245492979578713 277352805400684119734684035)
      ·
        refine ⟨416029208101026179602026053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277352805400684119734684035 416029208101026179602026053)
        ·
          refine ⟨78005476518942408675379885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 416029208101026179602026053 78005476518942408675379885)
          ·
            refine ⟨29252053694603403253267457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78005476518942408675379885 29252053694603403253267457)
            ·
              refine ⟨21939040270952552439950593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29252053694603403253267457 21939040270952552439950593)
              ·
                refine ⟨16454280203214414329962945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21939040270952552439950593 16454280203214414329962945)
                ·
                  refine ⟨12340710152410810747472209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16454280203214414329962945 12340710152410810747472209)
                  ·
                    refine ⟨9255532614308108060604157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12340710152410810747472209 9255532614308108060604157)
                    ·
                      refine ⟨3470824730365540522726559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9255532614308108060604157 3470824730365540522726559)
                      ·
                        rfl

theorem cell23_6759407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_6759407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759407 prefixEnd_6759407 := by exact prefixLift 6759407
  have htrace : WordTrace (prefixWord ++ tailWord_6759407) baseStart_6759407 baseEnd_6759407 := by
    simpa [prefixWord, tailWord_6759407, baseEnd_6759407] using wordTrace_append hprefix tailTrace_6759407
  have hstable : (prefixWord ++ tailWord_6759407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759407).length < 2 ^ (prefixWord ++ tailWord_6759407).sum := by decide
  have hdescent : baseEnd_6759407 < baseStart_6759407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759578 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6759578 : Nat := 118140960795 + 6759578 * 2 ^ 59
def prefixEnd_6759578 : Nat := 4983230072969 + 3 ^ 40 * 6759578 * 2
def baseEnd_6759578 : Nat := 3470912535557459353688273

theorem tailTrace_6759578 : CollatzResearch.WordTrace tailWord_6759578 prefixEnd_6759578 3470912535557459353688273 := by
  unfold tailWord_6759578
  simp only [CollatzResearch.WordTrace]
  refine ⟨61635515976302706214381847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164361375936807216571684925 61635515976302706214381847)
  ·
    refine ⟨92453273964454059321572771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61635515976302706214381847 92453273964454059321572771)
    ·
      refine ⟨138679910946681088982359157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92453273964454059321572771 138679910946681088982359157)
      ·
        refine ⟨13001241651251352092096171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138679910946681088982359157 13001241651251352092096171)
        ·
          refine ⟨19501862476877028138144257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13001241651251352092096171 19501862476877028138144257)
          ·
            refine ⟨14626396857657771103608193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19501862476877028138144257 14626396857657771103608193)
            ·
              refine ⟨10969797643243328327706145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14626396857657771103608193 10969797643243328327706145)
              ·
                refine ⟨8227348232432496245779609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10969797643243328327706145 8227348232432496245779609)
                ·
                  refine ⟨6170511174324372184334707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8227348232432496245779609 6170511174324372184334707)
                  ·
                    refine ⟨9255766761486558276502061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6170511174324372184334707 9255766761486558276502061)
                    ·
                      refine ⟨3470912535557459353688273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9255766761486558276502061 3470912535557459353688273)
                      ·
                        rfl

theorem cell23_6759578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6759578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759578 prefixEnd_6759578 := by exact prefixLift 6759578
  have htrace : WordTrace (prefixWord ++ tailWord_6759578) baseStart_6759578 baseEnd_6759578 := by
    simpa [prefixWord, tailWord_6759578, baseEnd_6759578] using wordTrace_append hprefix tailTrace_6759578
  have hstable : (prefixWord ++ tailWord_6759578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759578).length < 2 ^ (prefixWord ++ tailWord_6759578).sum := by decide
  have hdescent : baseEnd_6759578 < baseStart_6759578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759584 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 3, 4, 2]
def baseStart_6759584 : Nat := 118140960795 + 6759584 * 2 ^ 59
def prefixEnd_6759584 : Nat := 4983230072969 + 3 ^ 40 * 6759584 * 2
def baseEnd_6759584 : Nat := 3470915616441386330213245

theorem tailTrace_6759584 : CollatzResearch.WordTrace tailWord_6759584 prefixEnd_6759584 3470915616441386330213245 := by
  unfold tailWord_6759584
  simp only [CollatzResearch.WordTrace]
  refine ⟨123271141371594543941122903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164361521828792725254830537 123271141371594543941122903)
  ·
    refine ⟨184906712057391815911684355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123271141371594543941122903 184906712057391815911684355)
    ·
      refine ⟨277360068086087723867526533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184906712057391815911684355 277360068086087723867526533)
      ·
        refine ⟨52005012766141448225161225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277360068086087723867526533 52005012766141448225161225)
        ·
          refine ⟨39003759574606086168870919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52005012766141448225161225 39003759574606086168870919)
          ·
            refine ⟨58505639361909129253306379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39003759574606086168870919 58505639361909129253306379)
            ·
              refine ⟨87758459042863693879959569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58505639361909129253306379 87758459042863693879959569)
              ·
                refine ⟨65818844282147770409969677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87758459042863693879959569 65818844282147770409969677)
                ·
                  refine ⟨24682066605805413903738629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65818844282147770409969677 24682066605805413903738629)
                  ·
                    refine ⟨4627887488588515106950993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24682066605805413903738629 4627887488588515106950993)
                    ·
                      refine ⟨3470915616441386330213245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627887488588515106950993 3470915616441386330213245)
                      ·
                        rfl

theorem cell23_6759584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_6759584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759584 prefixEnd_6759584 := by exact prefixLift 6759584
  have htrace : WordTrace (prefixWord ++ tailWord_6759584) baseStart_6759584 baseEnd_6759584 := by
    simpa [prefixWord, tailWord_6759584, baseEnd_6759584] using wordTrace_append hprefix tailTrace_6759584
  have hstable : (prefixWord ++ tailWord_6759584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759584).length < 2 ^ (prefixWord ++ tailWord_6759584).sum := by decide
  have hdescent : baseEnd_6759584 < baseStart_6759584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759594 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_6759594 : Nat := 118140960795 + 6759594 * 2 ^ 59
def prefixEnd_6759594 : Nat := 4983230072969 + 3 ^ 40 * 6759594 * 2
def baseEnd_6759594 : Nat := 1156973583749310430362733

theorem tailTrace_6759594 : CollatzResearch.WordTrace tailWord_6759594 prefixEnd_6759594 1156973583749310430362733 := by
  unfold tailWord_6759594
  simp only [CollatzResearch.WordTrace]
  refine ⟨61635661868288214897527459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164361764982101906393406557 61635661868288214897527459)
  ·
    refine ⟨92453492802432322346291189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61635661868288214897527459 92453492802432322346291189)
    ·
      refine ⟨8667514950228030219964799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92453492802432322346291189 8667514950228030219964799)
      ·
        refine ⟨13001272425342045329947199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667514950228030219964799 13001272425342045329947199)
        ·
          refine ⟨19501908638013067994920799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13001272425342045329947199 19501908638013067994920799)
          ·
            refine ⟨29252862957019601992381199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19501908638013067994920799 29252862957019601992381199)
            ·
              refine ⟨43879294435529402988571799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29252862957019601992381199 43879294435529402988571799)
              ·
                refine ⟨65818941653294104482857699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43879294435529402988571799 65818941653294104482857699)
                ·
                  refine ⟨98728412479941156724286549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65818941653294104482857699 98728412479941156724286549)
                  ·
                    refine ⟨1156973583749310430362733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98728412479941156724286549 1156973583749310430362733)
                    ·
                      rfl

theorem cell23_6759594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_6759594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759594 prefixEnd_6759594 := by exact prefixLift 6759594
  have htrace : WordTrace (prefixWord ++ tailWord_6759594) baseStart_6759594 baseEnd_6759594 := by
    simpa [prefixWord, tailWord_6759594, baseEnd_6759594] using wordTrace_append hprefix tailTrace_6759594
  have hstable : (prefixWord ++ tailWord_6759594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759594).length < 2 ^ (prefixWord ++ tailWord_6759594).sum := by decide
  have hdescent : baseEnd_6759594 < baseStart_6759594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759601 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6759601 : Nat := 118140960795 + 6759601 * 2 ^ 59
def prefixEnd_6759601 : Nat := 4983230072969 + 3 ^ 40 * 6759601 * 2
def baseEnd_6759601 : Nat := 3470924345612512763700667

theorem tailTrace_6759601 : CollatzResearch.WordTrace tailWord_6759601 prefixEnd_6759601 3470924345612512763700667 := by
  unfold tailWord_6759601
  simp only [CollatzResearch.WordTrace]
  refine ⟨246542902784127499785614657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164361935189418333190409771 246542902784127499785614657)
  ·
    refine ⟨184907177088095624839210993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246542902784127499785614657 184907177088095624839210993)
    ·
      refine ⟨138680382816071718629408245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184907177088095624839210993 138680382816071718629408245)
      ·
        refine ⟨13001285889006723621507023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138680382816071718629408245 13001285889006723621507023)
        ·
          refine ⟨19501928833510085432260535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13001285889006723621507023 19501928833510085432260535)
          ·
            refine ⟨29252893250265128148390803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19501928833510085432260535 29252893250265128148390803)
            ·
              refine ⟨43879339875397692222586205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29252893250265128148390803 43879339875397692222586205)
              ·
                refine ⟨16454752453274134583469827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43879339875397692222586205 16454752453274134583469827)
                ·
                  refine ⟨24682128679911201875204741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16454752453274134583469827 24682128679911201875204741)
                  ·
                    refine ⟨4627899127483350351600889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24682128679911201875204741 4627899127483350351600889)
                    ·
                      refine ⟨3470924345612512763700667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4627899127483350351600889 3470924345612512763700667)
                      ·
                        rfl

theorem cell23_6759601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6759601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759601 prefixEnd_6759601 := by exact prefixLift 6759601
  have htrace : WordTrace (prefixWord ++ tailWord_6759601) baseStart_6759601 baseEnd_6759601 := by
    simpa [prefixWord, tailWord_6759601, baseEnd_6759601] using wordTrace_append hprefix tailTrace_6759601
  have hstable : (prefixWord ++ tailWord_6759601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759601).length < 2 ^ (prefixWord ++ tailWord_6759601).sum := by decide
  have hdescent : baseEnd_6759601 < baseStart_6759601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759607 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 7]
def baseStart_6759607 : Nat := 118140960795 + 6759607 * 2 ^ 59
def prefixEnd_6759607 : Nat := 4983230072969 + 3 ^ 40 * 6759607 * 2
def baseEnd_6759607 : Nat := 385658602944048860025071

theorem tailTrace_6759607 : CollatzResearch.WordTrace tailWord_6759607 prefixEnd_6759607 385658602944048860025071 := by
  unfold tailWord_6759607
  simp only [CollatzResearch.WordTrace]
  refine ⟨246543121622105762810333075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164362081081403841873555383 246543121622105762810333075)
  ·
    refine ⟨369814682433158644215499613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246543121622105762810333075 369814682433158644215499613)
    ·
      refine ⟨138680505912434491580812355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369814682433158644215499613 138680505912434491580812355)
      ·
        refine ⟨208020758868651737371218533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138680505912434491580812355 208020758868651737371218533)
        ·
          refine ⟨39003892287872200757103475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208020758868651737371218533 39003892287872200757103475)
          ·
            refine ⟨58505838431808301135655213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39003892287872200757103475 58505838431808301135655213)
            ·
              refine ⟨21939689411928112925870705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58505838431808301135655213 21939689411928112925870705)
              ·
                refine ⟨16454767058946084694403029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21939689411928112925870705 16454767058946084694403029)
                ·
                  refine ⟨385658602944048860025071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16454767058946084694403029 385658602944048860025071)
                  ·
                    rfl

theorem cell23_6759607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 7].length) (baseStart_6759607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759607 prefixEnd_6759607 := by exact prefixLift 6759607
  have htrace : WordTrace (prefixWord ++ tailWord_6759607) baseStart_6759607 baseEnd_6759607 := by
    simpa [prefixWord, tailWord_6759607, baseEnd_6759607] using wordTrace_append hprefix tailTrace_6759607
  have hstable : (prefixWord ++ tailWord_6759607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759607).length < 2 ^ (prefixWord ++ tailWord_6759607).sum := by decide
  have hdescent : baseEnd_6759607 < baseStart_6759607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759624 : List Nat := [2, 1, 3, 1, 2, 1, 3, 5, 5]
def baseStart_6759624 : Nat := 118140960795 + 6759624 * 2 ^ 59
def prefixEnd_6759624 : Nat := 4983230072969 + 3 ^ 40 * 6759624 * 2
def baseEnd_6759624 : Nat := 385659572851951797079229

theorem tailTrace_6759624 : CollatzResearch.WordTrace tailWord_6759624 prefixEnd_6759624 385659572851951797079229 := by
  unfold tailWord_6759624
  simp only [CollatzResearch.WordTrace]
  refine ⟨123271870831522087356850963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164362494442029449809134617 123271870831522087356850963)
  ·
    refine ⟨184907806247283131035276445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123271870831522087356850963 184907806247283131035276445)
    ·
      refine ⟨69340427342731174138228667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184907806247283131035276445 69340427342731174138228667)
      ·
        refine ⟨104010641014096761207343001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69340427342731174138228667 104010641014096761207343001)
        ·
          refine ⟨78007980760572570905507251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104010641014096761207343001 78007980760572570905507251)
          ·
            refine ⟨117011971140858856358260877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78007980760572570905507251 117011971140858856358260877)
            ·
              refine ⟨43879489177822071134347829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117011971140858856358260877 43879489177822071134347829)
              ·
                refine ⟨4113702110420819168845109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43879489177822071134347829 4113702110420819168845109)
                ·
                  refine ⟨385659572851951797079229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4113702110420819168845109 385659572851951797079229)
                  ·
                    rfl

theorem cell23_6759624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 5].length) (baseStart_6759624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759624 prefixEnd_6759624 := by exact prefixLift 6759624
  have htrace : WordTrace (prefixWord ++ tailWord_6759624) baseStart_6759624 baseEnd_6759624 := by
    simpa [prefixWord, tailWord_6759624, baseEnd_6759624] using wordTrace_append hprefix tailTrace_6759624
  have hstable : (prefixWord ++ tailWord_6759624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759624).length < 2 ^ (prefixWord ++ tailWord_6759624).sum := by decide
  have hdescent : baseEnd_6759624 < baseStart_6759624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759629 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6759629 : Nat := 118140960795 + 6759629 * 2 ^ 59
def prefixEnd_6759629 : Nat := 4983230072969 + 3 ^ 40 * 6759629 * 2
def baseEnd_6759629 : Nat := 3470938723070838654150539

theorem tailTrace_6759629 : CollatzResearch.WordTrace tailWord_6759629 prefixEnd_6759629 3470938723070838654150539 := by
  unfold tailWord_6759629
  simp only [CollatzResearch.WordTrace]
  refine ⟨246543924028026060567633941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164362616018684040378422627 246543924028026060567633941)
  ·
    refine ⟨11556746438813721589107841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 246543924028026060567633941 11556746438813721589107841)
    ·
      refine ⟨8667559829110291191830881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11556746438813721589107841 8667559829110291191830881)
      ·
        refine ⟨6500669871832718393873161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8667559829110291191830881 6500669871832718393873161)
        ·
          refine ⟨4875502403874538795404871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6500669871832718393873161 4875502403874538795404871)
          ·
            refine ⟨7313253605811808193107307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4875502403874538795404871 7313253605811808193107307)
            ·
              refine ⟨10969880408717712289660961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7313253605811808193107307 10969880408717712289660961)
              ·
                refine ⟨8227410306538284217245721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10969880408717712289660961 8227410306538284217245721)
                ·
                  refine ⟨6170557729903713162934291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8227410306538284217245721 6170557729903713162934291)
                  ·
                    refine ⟨9255836594855569744401437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6170557729903713162934291 9255836594855569744401437)
                    ·
                      refine ⟨3470938723070838654150539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9255836594855569744401437 3470938723070838654150539)
                      ·
                        rfl

theorem cell23_6759629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6759629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759629 prefixEnd_6759629 := by exact prefixLift 6759629
  have htrace : WordTrace (prefixWord ++ tailWord_6759629) baseStart_6759629 baseEnd_6759629 := by
    simpa [prefixWord, tailWord_6759629, baseEnd_6759629] using wordTrace_append hprefix tailTrace_6759629
  have hstable : (prefixWord ++ tailWord_6759629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759629).length < 2 ^ (prefixWord ++ tailWord_6759629).sum := by decide
  have hdescent : baseEnd_6759629 < baseStart_6759629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759634 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_6759634 : Nat := 118140960795 + 6759634 * 2 ^ 59
def prefixEnd_6759634 : Nat := 4983230072969 + 3 ^ 40 * 6759634 * 2
def baseEnd_6759634 : Nat := 3470941290474111134588015

theorem tailTrace_6759634 : CollatzResearch.WordTrace tailWord_6759634 prefixEnd_6759634 3470941290474111134588015 := by
  unfold tailWord_6759634
  simp only [CollatzResearch.WordTrace]
  refine ⟨61636026598251986605391489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164362737595338630947710637 61636026598251986605391489)
  ·
    refine ⟨46227019948688989954043617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61636026598251986605391489 46227019948688989954043617)
    ·
      refine ⟨34670264961516742465532713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46227019948688989954043617 34670264961516742465532713)
      ·
        refine ⟨26002698721137556849149535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34670264961516742465532713 26002698721137556849149535)
        ·
          refine ⟨39004048081706335273724303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26002698721137556849149535 39004048081706335273724303)
          ·
            refine ⟨58506072122559502910586455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39004048081706335273724303 58506072122559502910586455)
            ·
              refine ⟨87759108183839254365879683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58506072122559502910586455 87759108183839254365879683)
              ·
                refine ⟨131638662275758881548819525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87759108183839254365879683 131638662275758881548819525)
                ·
                  refine ⟨24682249176704790290403661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131638662275758881548819525 24682249176704790290403661)
                  ·
                    refine ⟨9255843441264296358901373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24682249176704790290403661 9255843441264296358901373)
                    ·
                      refine ⟨3470941290474111134588015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9255843441264296358901373 3470941290474111134588015)
                      ·
                        rfl

theorem cell23_6759634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_6759634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759634 prefixEnd_6759634 := by exact prefixLift 6759634
  have htrace : WordTrace (prefixWord ++ tailWord_6759634) baseStart_6759634 baseEnd_6759634 := by
    simpa [prefixWord, tailWord_6759634, baseEnd_6759634] using wordTrace_append hprefix tailTrace_6759634
  have hstable : (prefixWord ++ tailWord_6759634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759634).length < 2 ^ (prefixWord ++ tailWord_6759634).sum := by decide
  have hdescent : baseEnd_6759634 < baseStart_6759634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759647 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_6759647 : Nat := 118140960795 + 6759647 * 2 ^ 59
def prefixEnd_6759647 : Nat := 4983230072969 + 3 ^ 40 * 6759647 * 2
def baseEnd_6759647 : Nat := 3470947965722619583725455

theorem tailTrace_6759647 : CollatzResearch.WordTrace tailWord_6759647 prefixEnd_6759647 3470947965722619583725455 := by
  unfold tailWord_6759647
  simp only [CollatzResearch.WordTrace]
  refine ⟨246544580541960849641789195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164363053694640566427859463 246544580541960849641789195)
  ·
    refine ⟨369816870812941274462683793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246544580541960849641789195 369816870812941274462683793)
    ·
      refine ⟨277362653109705955847012845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369816870812941274462683793 277362653109705955847012845)
      ·
        refine ⟨104010994916139733442629817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277362653109705955847012845 104010994916139733442629817)
        ·
          refine ⟨78008246187104800081972363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104010994916139733442629817 78008246187104800081972363)
          ·
            refine ⟨117012369280657200122958545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78008246187104800081972363 117012369280657200122958545)
            ·
              refine ⟨87759276960492900092218909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117012369280657200122958545 87759276960492900092218909)
              ·
                refine ⟨32909728860184837534582091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87759276960492900092218909 32909728860184837534582091)
                ·
                  refine ⟨49364593290277256301873137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32909728860184837534582091 49364593290277256301873137)
                  ·
                    refine ⟨37023444967707942226404853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49364593290277256301873137 37023444967707942226404853)
                    ·
                      refine ⟨3470947965722619583725455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37023444967707942226404853 3470947965722619583725455)
                      ·
                        rfl

theorem cell23_6759647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_6759647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759647 prefixEnd_6759647 := by exact prefixLift 6759647
  have htrace : WordTrace (prefixWord ++ tailWord_6759647) baseStart_6759647 baseEnd_6759647 := by
    simpa [prefixWord, tailWord_6759647, baseEnd_6759647] using wordTrace_append hprefix tailTrace_6759647
  have hstable : (prefixWord ++ tailWord_6759647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759647).length < 2 ^ (prefixWord ++ tailWord_6759647).sum := by decide
  have hdescent : baseEnd_6759647 < baseStart_6759647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759674 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_6759674 : Nat := 118140960795 + 6759674 * 2 ^ 59
def prefixEnd_6759674 : Nat := 4983230072969 + 3 ^ 40 * 6759674 * 2
def baseEnd_6759674 : Nat := 3470961829700290978087831

theorem tailTrace_6759674 : CollatzResearch.WordTrace tailWord_6759674 prefixEnd_6759674 3470961829700290978087831 := by
  unfold tailWord_6759674
  simp only [CollatzResearch.WordTrace]
  refine ⟨61636391328215758313255519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164363710208575355502014717 61636391328215758313255519)
  ·
    refine ⟨92454586992323637469883279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61636391328215758313255519 92454586992323637469883279)
    ·
      refine ⟨138681880488485456204824919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92454586992323637469883279 138681880488485456204824919)
      ·
        refine ⟨208022820732728184307237379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138681880488485456204824919 208022820732728184307237379)
        ·
          refine ⟨312034231099092276460856069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208022820732728184307237379 312034231099092276460856069)
          ·
            refine ⟨58506418331079801836410513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312034231099092276460856069 58506418331079801836410513)
            ·
              refine ⟨43879813748309851377307885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58506418331079801836410513 43879813748309851377307885)
              ·
                refine ⟨16454930155616194266490457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43879813748309851377307885 16454930155616194266490457)
                ·
                  refine ⟨12341197616712145699867843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16454930155616194266490457 12341197616712145699867843)
                  ·
                    refine ⟨18511796425068218549801765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12341197616712145699867843 18511796425068218549801765)
                    ·
                      refine ⟨3470961829700290978087831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18511796425068218549801765 3470961829700290978087831)
                      ·
                        rfl

theorem cell23_6759674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_6759674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759674 prefixEnd_6759674 := by exact prefixLift 6759674
  have htrace : WordTrace (prefixWord ++ tailWord_6759674) baseStart_6759674 baseEnd_6759674 := by
    simpa [prefixWord, tailWord_6759674, baseEnd_6759674] using wordTrace_append hprefix tailTrace_6759674
  have hstable : (prefixWord ++ tailWord_6759674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759674).length < 2 ^ (prefixWord ++ tailWord_6759674).sum := by decide
  have hdescent : baseEnd_6759674 < baseStart_6759674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759677 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_6759677 : Nat := 118140960795 + 6759677 * 2 ^ 59
def prefixEnd_6759677 : Nat := 4983230072969 + 3 ^ 40 * 6759677 * 2
def baseEnd_6759677 : Nat := 3470963370142254466350317

theorem tailTrace_6759677 : CollatzResearch.WordTrace tailWord_6759677 prefixEnd_6759677 3470963370142254466350317 := by
  unfold tailWord_6759677
  simp only [CollatzResearch.WordTrace]
  refine ⟨246545674731852164765381285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164363783154568109843587523 246545674731852164765381285)
  ·
    refine ⟨46227314012222280893508991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246545674731852164765381285 46227314012222280893508991)
    ·
      refine ⟨69340971018333421340263487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46227314012222280893508991 69340971018333421340263487)
      ·
        refine ⟨104011456527500132010395231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69340971018333421340263487 104011456527500132010395231)
        ·
          refine ⟨156017184791250198015592847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104011456527500132010395231 156017184791250198015592847)
          ·
            refine ⟨234025777186875297023389271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156017184791250198015592847 234025777186875297023389271)
            ·
              refine ⟨351038665780312945535083907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234025777186875297023389271 351038665780312945535083907)
              ·
                refine ⟨526557998670469418302625861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351038665780312945535083907 526557998670469418302625861)
                ·
                  refine ⟨98729624750713015931742349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526557998670469418302625861 98729624750713015931742349)
                  ·
                    refine ⟨37023609281517380974403381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98729624750713015931742349 37023609281517380974403381)
                    ·
                      refine ⟨3470963370142254466350317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37023609281517380974403381 3470963370142254466350317)
                      ·
                        rfl

theorem cell23_6759677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_6759677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759677 prefixEnd_6759677 := by exact prefixLift 6759677
  have htrace : WordTrace (prefixWord ++ tailWord_6759677) baseStart_6759677 baseEnd_6759677 := by
    simpa [prefixWord, tailWord_6759677, baseEnd_6759677] using wordTrace_append hprefix tailTrace_6759677
  have hstable : (prefixWord ++ tailWord_6759677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759677).length < 2 ^ (prefixWord ++ tailWord_6759677).sum := by decide
  have hdescent : baseEnd_6759677 < baseStart_6759677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759697 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 8]
def baseStart_6759697 : Nat := 118140960795 + 6759697 * 2 ^ 59
def prefixEnd_6759697 : Nat := 4983230072969 + 3 ^ 40 * 6759697 * 2
def baseEnd_6759697 : Nat := 385663737750593820900025

theorem tailTrace_6759697 : CollatzResearch.WordTrace tailWord_6759697 prefixEnd_6759697 385663737750593820900025 := by
  unfold tailWord_6759697
  simp only [CollatzResearch.WordTrace]
  refine ⟨246546404191779708181109345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164364269461186472120739563 246546404191779708181109345)
  ·
    refine ⟨184909803143834781135832009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246546404191779708181109345 184909803143834781135832009)
    ·
      refine ⟨138682352357876085851874007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184909803143834781135832009 138682352357876085851874007)
      ·
        refine ⟨208023528536814128777811011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138682352357876085851874007 208023528536814128777811011)
        ·
          refine ⟨312035292805221193166716517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208023528536814128777811011 312035292805221193166716517)
          ·
            refine ⟨58506617400978973718759347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312035292805221193166716517 58506617400978973718759347)
            ·
              refine ⟨87759926101468460578139021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58506617400978973718759347 87759926101468460578139021)
              ·
                refine ⟨32909972288050672716802133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87759926101468460578139021 32909972288050672716802133)
                ·
                  refine ⟨385663737750593820900025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32909972288050672716802133 385663737750593820900025)
                  ·
                    rfl

theorem cell23_6759697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 8].length) (baseStart_6759697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759697 prefixEnd_6759697 := by exact prefixLift 6759697
  have htrace : WordTrace (prefixWord ++ tailWord_6759697) baseStart_6759697 baseEnd_6759697 := by
    simpa [prefixWord, tailWord_6759697, baseEnd_6759697] using wordTrace_append hprefix tailTrace_6759697
  have hstable : (prefixWord ++ tailWord_6759697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759697).length < 2 ^ (prefixWord ++ tailWord_6759697).sum := by decide
  have hdescent : baseEnd_6759697 < baseStart_6759697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759698 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6759698 : Nat := 118140960795 + 6759698 * 2 ^ 59
def prefixEnd_6759698 : Nat := 4983230072969 + 3 ^ 40 * 6759698 * 2
def baseEnd_6759698 : Nat := 3470974153235998884187721

theorem tailTrace_6759698 : CollatzResearch.WordTrace tailWord_6759698 prefixEnd_6759698 3470974153235998884187721 := by
  unfold tailWord_6759698
  simp only [CollatzResearch.WordTrace]
  refine ⟨61636610166194021337973937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164364293776517390234597165 61636610166194021337973937)
  ·
    refine ⟨46227457624645516003480453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61636610166194021337973937 46227457624645516003480453)
    ·
      refine ⟨8667648304621034250652585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46227457624645516003480453 8667648304621034250652585)
      ·
        refine ⟨6500736228465775687989439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8667648304621034250652585 6500736228465775687989439)
        ·
          refine ⟨9751104342698663531984159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6500736228465775687989439 9751104342698663531984159)
          ·
            refine ⟨14626656514047995297976239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9751104342698663531984159 14626656514047995297976239)
            ·
              refine ⟨21939984771071992946964359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14626656514047995297976239 21939984771071992946964359)
              ·
                refine ⟨32909977156607989420446539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21939984771071992946964359 32909977156607989420446539)
                ·
                  refine ⟨49364965734911984130669809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32909977156607989420446539 49364965734911984130669809)
                  ·
                    refine ⟨37023724301183988098002357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49364965734911984130669809 37023724301183988098002357)
                    ·
                      refine ⟨3470974153235998884187721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37023724301183988098002357 3470974153235998884187721)
                      ·
                        rfl

theorem cell23_6759698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6759698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759698 prefixEnd_6759698 := by exact prefixLift 6759698
  have htrace : WordTrace (prefixWord ++ tailWord_6759698) baseStart_6759698 baseEnd_6759698 := by
    simpa [prefixWord, tailWord_6759698, baseEnd_6759698] using wordTrace_append hprefix tailTrace_6759698
  have hstable : (prefixWord ++ tailWord_6759698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759698).length < 2 ^ (prefixWord ++ tailWord_6759698).sum := by decide
  have hdescent : baseEnd_6759698 < baseStart_6759698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759748 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 6]
def baseStart_6759748 : Nat := 118140960795 + 6759748 * 2 ^ 59
def prefixEnd_6759748 : Nat := 4983230072969 + 3 ^ 40 * 6759748 * 2
def baseEnd_6759748 : Nat := 385666647474302632062499

theorem tailTrace_6759748 : CollatzResearch.WordTrace tailWord_6759748 prefixEnd_6759748 385666647474302632062499 := by
  unfold tailWord_6759748
  simp only [CollatzResearch.WordTrace]
  refine ⟨123274132157297471945607949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164365509543063295927477265 123274132157297471945607949)
  ·
    refine ⟨46227799558986551979602981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123274132157297471945607949 46227799558986551979602981)
    ·
      refine ⟨8667712417309978496175559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46227799558986551979602981 8667712417309978496175559)
      ·
        refine ⟨13001568625964967744263339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667712417309978496175559 13001568625964967744263339)
        ·
          refine ⟨19502352938947451616395009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13001568625964967744263339 19502352938947451616395009)
          ·
            refine ⟨14626764704210588712296257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19502352938947451616395009 14626764704210588712296257)
            ·
              refine ⟨10970073528157941534222193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14626764704210588712296257 10970073528157941534222193)
              ·
                refine ⟨8227555146118456150666645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10970073528157941534222193 8227555146118456150666645)
                ·
                  refine ⟨385666647474302632062499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8227555146118456150666645 385666647474302632062499)
                  ·
                    rfl

theorem cell23_6759748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_6759748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759748 prefixEnd_6759748 := by exact prefixLift 6759748
  have htrace : WordTrace (prefixWord ++ tailWord_6759748) baseStart_6759748 baseEnd_6759748 := by
    simpa [prefixWord, tailWord_6759748, baseEnd_6759748] using wordTrace_append hprefix tailTrace_6759748
  have hstable : (prefixWord ++ tailWord_6759748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759748).length < 2 ^ (prefixWord ++ tailWord_6759748).sum := by decide
  have hdescent : baseEnd_6759748 < baseStart_6759748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759781 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 4]
def baseStart_6759781 : Nat := 118140960795 + 6759781 * 2 ^ 59
def prefixEnd_6759781 : Nat := 4983230072969 + 3 ^ 40 * 6759781 * 2
def baseEnd_6759781 : Nat := 3471016772130322059449839

theorem tailTrace_6759781 : CollatzResearch.WordTrace tailWord_6759781 prefixEnd_6759781 3471016772130322059449839 := by
  unfold tailWord_6759781
  simp only [CollatzResearch.WordTrace]
  refine ⟨246549467923475390527167197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164366311948983593684778131 246549467923475390527167197)
  ·
    refine ⟨92456050471303271447687699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246549467923475390527167197 92456050471303271447687699)
    ·
      refine ⟨138684075706954907171531549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92456050471303271447687699 138684075706954907171531549)
      ·
        refine ⟨52006528390108090189324331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138684075706954907171531549 52006528390108090189324331)
        ·
          refine ⟨78009792585162135283986497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52006528390108090189324331 78009792585162135283986497)
          ·
            refine ⟨58507344438871601462989873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78009792585162135283986497 58507344438871601462989873)
            ·
              refine ⟨43880508329153701097242405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58507344438871601462989873 43880508329153701097242405)
              ·
                refine ⟨8227595311716318955732951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43880508329153701097242405 8227595311716318955732951)
                ·
                  refine ⟨12341392967574478433599427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8227595311716318955732951 12341392967574478433599427)
                  ·
                    refine ⟨18512089451361717650399141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12341392967574478433599427 18512089451361717650399141)
                    ·
                      refine ⟨3471016772130322059449839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18512089451361717650399141 3471016772130322059449839)
                      ·
                        rfl

theorem cell23_6759781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_6759781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759781 prefixEnd_6759781 := by exact prefixLift 6759781
  have htrace : WordTrace (prefixWord ++ tailWord_6759781) baseStart_6759781 baseEnd_6759781 := by
    simpa [prefixWord, tailWord_6759781, baseEnd_6759781] using wordTrace_append hprefix tailTrace_6759781
  have hstable : (prefixWord ++ tailWord_6759781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759781).length < 2 ^ (prefixWord ++ tailWord_6759781).sum := by decide
  have hdescent : baseEnd_6759781 < baseStart_6759781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759815 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_6759815 : Nat := 118140960795 + 6759815 * 2 ^ 59
def prefixEnd_6759815 : Nat := 4983230072969 + 3 ^ 40 * 6759815 * 2
def baseEnd_6759815 : Nat := 3471034230472574926424683

theorem tailTrace_6759815 : CollatzResearch.WordTrace tailWord_6759815 prefixEnd_6759815 3471034230472574926424683 := by
  unfold tailWord_6759815
  simp only [CollatzResearch.WordTrace]
  refine ⟨246550708005352214333904899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164367138670234809555936599 246550708005352214333904899)
  ·
    refine ⟨369826062008028321500857349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246550708005352214333904899 369826062008028321500857349)
    ·
      refine ⟨69342386626505310281410753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369826062008028321500857349 69342386626505310281410753)
      ·
        refine ⟨52006789969878982711058065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69342386626505310281410753 52006789969878982711058065)
        ·
          refine ⟨39005092477409237033293549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52006789969878982711058065 39005092477409237033293549)
          ·
            refine ⟨14626909679028463887485081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39005092477409237033293549 14626909679028463887485081)
            ·
              refine ⟨10970182259271347915613811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14626909679028463887485081 10970182259271347915613811)
              ·
                refine ⟨16455273388907021873420717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10970182259271347915613811 16455273388907021873420717)
                ·
                  refine ⟨6170727520840133202532769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16455273388907021873420717 6170727520840133202532769)
                  ·
                    refine ⟨4628045640630099901899577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6170727520840133202532769 4628045640630099901899577)
                    ·
                      refine ⟨3471034230472574926424683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628045640630099901899577 3471034230472574926424683)
                      ·
                        rfl

theorem cell23_6759815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_6759815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759815 prefixEnd_6759815 := by exact prefixLift 6759815
  have htrace : WordTrace (prefixWord ++ tailWord_6759815) baseStart_6759815 baseEnd_6759815 := by
    simpa [prefixWord, tailWord_6759815, baseEnd_6759815] using wordTrace_append hprefix tailTrace_6759815
  have hstable : (prefixWord ++ tailWord_6759815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759815).length < 2 ^ (prefixWord ++ tailWord_6759815).sum := by decide
  have hdescent : baseEnd_6759815 < baseStart_6759815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759828 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_6759828 : Nat := 118140960795 + 6759828 * 2 ^ 59
def prefixEnd_6759828 : Nat := 4983230072969 + 3 ^ 40 * 6759828 * 2
def baseEnd_6759828 : Nat := 3471040905721083375562123

theorem tailTrace_6759828 : CollatzResearch.WordTrace tailWord_6759828 prefixEnd_6759828 3471040905721083375562123 := by
  unfold tailWord_6759828
  simp only [CollatzResearch.WordTrace]
  refine ⟨123275591077152558777064069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164367454769536745036085425 123275591077152558777064069)
  ·
    refine ⟨23114173326966104770699513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123275591077152558777064069 23114173326966104770699513)
    ·
      refine ⟨17335629995224578578024635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23114173326966104770699513 17335629995224578578024635)
      ·
        refine ⟨26003444992836867867036953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17335629995224578578024635 26003444992836867867036953)
        ·
          refine ⟨19502583744627650900277715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26003444992836867867036953 19502583744627650900277715)
          ·
            refine ⟨29253875616941476350416573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19502583744627650900277715 29253875616941476350416573)
            ·
              refine ⟨10970203356353053631406215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29253875616941476350416573 10970203356353053631406215)
              ·
                refine ⟨16455305034529580447109323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10970203356353053631406215 16455305034529580447109323)
                ·
                  refine ⟨24682957551794370670663985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16455305034529580447109323 24682957551794370670663985)
                  ·
                    refine ⟨18512218163845778002997989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24682957551794370670663985 18512218163845778002997989)
                    ·
                      refine ⟨3471040905721083375562123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18512218163845778002997989 3471040905721083375562123)
                      ·
                        rfl

theorem cell23_6759828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_6759828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759828 prefixEnd_6759828 := by exact prefixLift 6759828
  have htrace : WordTrace (prefixWord ++ tailWord_6759828) baseStart_6759828 baseEnd_6759828 := by
    simpa [prefixWord, tailWord_6759828, baseEnd_6759828] using wordTrace_append hprefix tailTrace_6759828
  have hstable : (prefixWord ++ tailWord_6759828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759828).length < 2 ^ (prefixWord ++ tailWord_6759828).sum := by decide
  have hdescent : baseEnd_6759828 < baseStart_6759828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759838 : List Nat := [4, 3, 1, 2, 2, 1, 1, 9]
def baseStart_6759838 : Nat := 118140960795 + 6759838 * 2 ^ 59
def prefixEnd_6759838 : Nat := 4983230072969 + 3 ^ 40 * 6759838 * 2
def baseEnd_6759838 : Nat := 128557260760282530979151

theorem tailTrace_6759838 : CollatzResearch.WordTrace tailWord_6759838 prefixEnd_6759838 128557260760282530979151 := by
  unfold tailWord_6759838
  simp only [CollatzResearch.WordTrace]
  refine ⟨30818943360533611157749021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164367697922845926174661445 30818943360533611157749021)
  ·
    refine ⟨11557103760200104184155883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30818943360533611157749021 11557103760200104184155883)
    ·
      refine ⟨17335655640300156276233825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11557103760200104184155883 17335655640300156276233825)
      ·
        refine ⟨13001741730225117207175369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17335655640300156276233825 13001741730225117207175369)
        ·
          refine ⟨9751306297668837905381527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13001741730225117207175369 9751306297668837905381527)
          ·
            refine ⟨14626959446503256858072291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9751306297668837905381527 14626959446503256858072291)
            ·
              refine ⟨21940439169754885287108437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14626959446503256858072291 21940439169754885287108437)
              ·
                refine ⟨128557260760282530979151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21940439169754885287108437 128557260760282530979151)
                ·
                  rfl

theorem cell23_6759838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_6759838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759838 prefixEnd_6759838 := by exact prefixLift 6759838
  have htrace : WordTrace (prefixWord ++ tailWord_6759838) baseStart_6759838 baseEnd_6759838 := by
    simpa [prefixWord, tailWord_6759838, baseEnd_6759838] using wordTrace_append hprefix tailTrace_6759838
  have hstable : (prefixWord ++ tailWord_6759838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759838).length < 2 ^ (prefixWord ++ tailWord_6759838).sum := by decide
  have hdescent : baseEnd_6759838 < baseStart_6759838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759864 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 4, 6]
def baseStart_6759864 : Nat := 118140960795 + 6759864 * 2 ^ 59
def prefixEnd_6759864 : Nat := 4983230072969 + 3 ^ 40 * 6759864 * 2
def baseEnd_6759864 : Nat := 1157019797008215078237319

theorem tailTrace_6759864 : CollatzResearch.WordTrace tailWord_6759864 prefixEnd_6759864 1157019797008215078237319 := by
  unfold tailWord_6759864
  simp only [CollatzResearch.WordTrace]
  refine ⟨123276247591087347851219323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164368330121449797134959097 123276247591087347851219323)
  ·
    refine ⟨184914371386631021776828985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123276247591087347851219323 184914371386631021776828985)
    ·
      refine ⟨138685778539973266332621739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184914371386631021776828985 138685778539973266332621739)
      ·
        refine ⟨208028667809959899498932609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138685778539973266332621739 208028667809959899498932609)
        ·
          refine ⟨156021500857469924624199457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208028667809959899498932609 156021500857469924624199457)
          ·
            refine ⟨117016125643102443468149593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156021500857469924624199457 117016125643102443468149593)
            ·
              refine ⟨87762094232326832601112195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117016125643102443468149593 87762094232326832601112195)
              ·
                refine ⟨131643141348490248901668293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87762094232326832601112195 131643141348490248901668293)
                ·
                  refine ⟨24683089002841921669062805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131643141348490248901668293 24683089002841921669062805)
                  ·
                    refine ⟨1157019797008215078237319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24683089002841921669062805 1157019797008215078237319)
                    ·
                      rfl

theorem cell23_6759864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_6759864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759864 prefixEnd_6759864 := by exact prefixLift 6759864
  have htrace : WordTrace (prefixWord ++ tailWord_6759864) baseStart_6759864 baseEnd_6759864 := by
    simpa [prefixWord, tailWord_6759864, baseEnd_6759864] using wordTrace_append hprefix tailTrace_6759864
  have hstable : (prefixWord ++ tailWord_6759864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759864).length < 2 ^ (prefixWord ++ tailWord_6759864).sum := by decide
  have hdescent : baseEnd_6759864 < baseStart_6759864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759882 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_6759882 : Nat := 118140960795 + 6759882 * 2 ^ 59
def prefixEnd_6759882 : Nat := 4983230072969 + 3 ^ 40 * 6759882 * 2
def baseEnd_6759882 : Nat := 3471068633676426164286875

theorem tailTrace_6759882 : CollatzResearch.WordTrace tailWord_6759882 prefixEnd_6759882 3471068633676426164286875 := by
  unfold tailWord_6759882
  simp only [CollatzResearch.WordTrace]
  refine ⟨61638287924027371194148475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164368767797406323184395933 61638287924027371194148475)
  ·
    refine ⟨92457431886041056791222713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61638287924027371194148475 92457431886041056791222713)
    ·
      refine ⟨69343073914530792593417035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92457431886041056791222713 69343073914530792593417035)
      ·
        refine ⟨104014610871796188890125553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69343073914530792593417035 104014610871796188890125553)
        ·
          refine ⟨78010958153847141667594165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104014610871796188890125553 78010958153847141667594165)
          ·
            refine ⟨7313527326923169531336953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78010958153847141667594165 7313527326923169531336953)
            ·
              refine ⟨5485145495192377148502715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7313527326923169531336953 5485145495192377148502715)
              ·
                refine ⟨8227718242788565722754073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5485145495192377148502715 8227718242788565722754073)
                ·
                  refine ⟨6170788682091424292065555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8227718242788565722754073 6170788682091424292065555)
                  ·
                    refine ⟨9256183023137136438098333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6170788682091424292065555 9256183023137136438098333)
                    ·
                      refine ⟨3471068633676426164286875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9256183023137136438098333 3471068633676426164286875)
                      ·
                        rfl

theorem cell23_6759882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_6759882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759882 prefixEnd_6759882 := by exact prefixLift 6759882
  have htrace : WordTrace (prefixWord ++ tailWord_6759882) baseStart_6759882 baseEnd_6759882 := by
    simpa [prefixWord, tailWord_6759882, baseEnd_6759882] using wordTrace_append hprefix tailTrace_6759882
  have hstable : (prefixWord ++ tailWord_6759882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759882).length < 2 ^ (prefixWord ++ tailWord_6759882).sum := by decide
  have hdescent : baseEnd_6759882 < baseStart_6759882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759904 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_6759904 : Nat := 118140960795 + 6759904 * 2 ^ 59
def prefixEnd_6759904 : Nat := 4983230072969 + 3 ^ 40 * 6759904 * 2
def baseEnd_6759904 : Nat := 3471079930250825078211773

theorem tailTrace_6759904 : CollatzResearch.WordTrace tailWord_6759904 prefixEnd_6759904 3471079930250825078211773 := by
  unfold tailWord_6759904
  simp only [CollatzResearch.WordTrace]
  refine ⟨123276977051014891266947383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164369302734686521689263177 123276977051014891266947383)
  ·
    refine ⟨184915465576522336900421075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123276977051014891266947383 184915465576522336900421075)
    ·
      refine ⟨277373198364783505350631613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184915465576522336900421075 277373198364783505350631613)
      ·
        refine ⟨104014949386793814506486855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277373198364783505350631613 104014949386793814506486855)
        ·
          refine ⟨156022424080190721759730283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104014949386793814506486855 156022424080190721759730283)
          ·
            refine ⟨234033636120286082639595425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156022424080190721759730283 234033636120286082639595425)
            ·
              refine ⟨175525227090214561979696569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234033636120286082639595425 175525227090214561979696569)
              ·
                refine ⟨131643920317660921484772427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175525227090214561979696569 131643920317660921484772427)
                ·
                  refine ⟨197465880476491382227158641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131643920317660921484772427 197465880476491382227158641)
                  ·
                    refine ⟨148099410357368536670368981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197465880476491382227158641 148099410357368536670368981)
                    ·
                      refine ⟨3471079930250825078211773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148099410357368536670368981 3471079930250825078211773)
                      ·
                        rfl

theorem cell23_6759904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_6759904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759904 prefixEnd_6759904 := by exact prefixLift 6759904
  have htrace : WordTrace (prefixWord ++ tailWord_6759904) baseStart_6759904 baseEnd_6759904 := by
    simpa [prefixWord, tailWord_6759904, baseEnd_6759904] using wordTrace_append hprefix tailTrace_6759904
  have hstable : (prefixWord ++ tailWord_6759904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759904).length < 2 ^ (prefixWord ++ tailWord_6759904).sum := by decide
  have hdescent : baseEnd_6759904 < baseStart_6759904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759922 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_6759922 : Nat := 118140960795 + 6759922 * 2 ^ 59
def prefixEnd_6759922 : Nat := 4983230072969 + 3 ^ 40 * 6759922 * 2
def baseEnd_6759922 : Nat := 3471089172902606007786691

theorem tailTrace_6759922 : CollatzResearch.WordTrace tailWord_6759922 prefixEnd_6759922 3471089172902606007786691 := by
  unfold tailWord_6759922
  simp only [CollatzResearch.WordTrace]
  refine ⟨61638652653991142902012505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164369740410643047738700013 61638652653991142902012505)
  ·
    refine ⟨46228989490493357176509379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61638652653991142902012505 46228989490493357176509379)
    ·
      refine ⟨69343484235740035764764069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46228989490493357176509379 69343484235740035764764069)
      ·
        refine ⟨13001903294201256705893263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69343484235740035764764069 13001903294201256705893263)
        ·
          refine ⟨19502854941301885058839895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13001903294201256705893263 19502854941301885058839895)
          ·
            refine ⟨29254282411952827588259843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19502854941301885058839895 29254282411952827588259843)
            ·
              refine ⟨43881423617929241382389765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29254282411952827588259843 43881423617929241382389765)
              ·
                refine ⟨8227766928361732759198081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43881423617929241382389765 8227766928361732759198081)
                ·
                  refine ⟨6170825196271299569398561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8227766928361732759198081 6170825196271299569398561)
                  ·
                    refine ⟨4628118897203474677048921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6170825196271299569398561 4628118897203474677048921)
                    ·
                      refine ⟨3471089172902606007786691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628118897203474677048921 3471089172902606007786691)
                      ·
                        rfl

theorem cell23_6759922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_6759922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759922 prefixEnd_6759922 := by exact prefixLift 6759922
  have htrace : WordTrace (prefixWord ++ tailWord_6759922) baseStart_6759922 baseEnd_6759922 := by
    simpa [prefixWord, tailWord_6759922, baseEnd_6759922] using wordTrace_append hprefix tailTrace_6759922
  have hstable : (prefixWord ++ tailWord_6759922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759922).length < 2 ^ (prefixWord ++ tailWord_6759922).sum := by decide
  have hdescent : baseEnd_6759922 < baseStart_6759922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759928 : List Nat := [2, 1, 2, 1, 1, 6, 1, 4, 5]
def baseStart_6759928 : Nat := 118140960795 + 6759928 * 2 ^ 59
def prefixEnd_6759928 : Nat := 4983230072969 + 3 ^ 40 * 6759928 * 2
def baseEnd_6759928 : Nat := 385676917087392553812407

theorem tailTrace_6759928 : CollatzResearch.WordTrace tailWord_6759928 prefixEnd_6759928 385676917087392553812407 := by
  unfold tailWord_6759928
  simp only [CollatzResearch.WordTrace]
  refine ⟨123277414726971417316384219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164369886302628556421845625 123277414726971417316384219)
  ·
    refine ⟨184916122090457125974576329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123277414726971417316384219 184916122090457125974576329)
    ·
      refine ⟨138687091567842844480932247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184916122090457125974576329 138687091567842844480932247)
      ·
        refine ⟨208030637351764266721398371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138687091567842844480932247 208030637351764266721398371)
        ·
          refine ⟨312045956027646400082097557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208030637351764266721398371 312045956027646400082097557)
          ·
            refine ⟨14627154188795925003848323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 312045956027646400082097557 14627154188795925003848323)
            ·
              refine ⟨21940731283193887505772485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14627154188795925003848323 21940731283193887505772485)
              ·
                refine ⟨4113887115598853907332341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21940731283193887505772485 4113887115598853907332341)
                ·
                  refine ⟨385676917087392553812407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4113887115598853907332341 385676917087392553812407)
                  ·
                    rfl

theorem cell23_6759928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 5].length) (baseStart_6759928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759928 prefixEnd_6759928 := by exact prefixLift 6759928
  have htrace : WordTrace (prefixWord ++ tailWord_6759928) baseStart_6759928 baseEnd_6759928 := by
    simpa [prefixWord, tailWord_6759928, baseEnd_6759928] using wordTrace_append hprefix tailTrace_6759928
  have hstable : (prefixWord ++ tailWord_6759928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759928).length < 2 ^ (prefixWord ++ tailWord_6759928).sum := by decide
  have hdescent : baseEnd_6759928 < baseStart_6759928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6759978 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_6759978 : Nat := 118140960795 + 6759978 * 2 ^ 59
def prefixEnd_6759978 : Nat := 4983230072969 + 3 ^ 40 * 6759978 * 2
def baseEnd_6759978 : Nat := 3471117927819257788686433

theorem tailTrace_6759978 : CollatzResearch.WordTrace tailWord_6759978 prefixEnd_6759978 3471117927819257788686433 := by
  unfold tailWord_6759978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61639163275940423293022147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164371102069174462114725725 61639163275940423293022147)
  ·
    refine ⟨92458744913910634939533221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61639163275940423293022147 92458744913910634939533221)
    ·
      refine ⟨17336014671358244051162479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92458744913910634939533221 17336014671358244051162479)
      ·
        refine ⟨26004022007037366076743719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17336014671358244051162479 26004022007037366076743719)
        ·
          refine ⟨39006033010556049115115579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26004022007037366076743719 39006033010556049115115579)
          ·
            refine ⟨58509049515834073672673369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39006033010556049115115579 58509049515834073672673369)
            ·
              refine ⟨43881787136875555254505027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58509049515834073672673369 43881787136875555254505027)
              ·
                refine ⟨65822680705313332881757541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43881787136875555254505027 65822680705313332881757541)
                ·
                  refine ⟨12341752632246249915329539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65822680705313332881757541 12341752632246249915329539)
                  ·
                    refine ⟨18512628948369374872994309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12341752632246249915329539 18512628948369374872994309)
                    ·
                      refine ⟨3471117927819257788686433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18512628948369374872994309 3471117927819257788686433)
                      ·
                        rfl

theorem cell23_6759978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_6759978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6759978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6759978 prefixEnd_6759978 := by exact prefixLift 6759978
  have htrace : WordTrace (prefixWord ++ tailWord_6759978) baseStart_6759978 baseEnd_6759978 := by
    simpa [prefixWord, tailWord_6759978, baseEnd_6759978] using wordTrace_append hprefix tailTrace_6759978
  have hstable : (prefixWord ++ tailWord_6759978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6759978).length < 2 ^ (prefixWord ++ tailWord_6759978).sum := by decide
  have hdescent : baseEnd_6759978 < baseStart_6759978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6759978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760011 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 3]
def baseStart_6760011 : Nat := 118140960795 + 6760011 * 2 ^ 59
def prefixEnd_6760011 : Nat := 4983230072969 + 3 ^ 40 * 6760011 * 2
def baseEnd_6760011 : Nat := 3471134872680856159573781

theorem tailTrace_6760011 : CollatzResearch.WordTrace tailWord_6760011 prefixEnd_6760011 3471134872680856159573781 := by
  unfold tailWord_6760011
  simp only [CollatzResearch.WordTrace]
  refine ⟨246557856712642139808039887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164371904475094759872026591 246557856712642139808039887)
  ·
    refine ⟨369836785068963209712059831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246557856712642139808039887 369836785068963209712059831)
    ·
      refine ⟨554755177603444814568089747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369836785068963209712059831 554755177603444814568089747)
      ·
        refine ⟨832132766405167221852134621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554755177603444814568089747 832132766405167221852134621)
        ·
          refine ⟨312049787401937708194550483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 832132766405167221852134621 312049787401937708194550483)
          ·
            refine ⟨468074681102906562291825725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312049787401937708194550483 468074681102906562291825725)
            ·
              refine ⟨175528005413589960859434647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468074681102906562291825725 175528005413589960859434647)
              ·
                refine ⟨263292008120384941289151971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175528005413589960859434647 263292008120384941289151971)
                ·
                  refine ⟨394938012180577411933727957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263292008120384941289151971 394938012180577411933727957)
                  ·
                    refine ⟨9256359660482283092196749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 394938012180577411933727957 9256359660482283092196749)
                    ·
                      refine ⟨3471134872680856159573781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9256359660482283092196749 3471134872680856159573781)
                      ·
                        rfl

theorem cell23_6760011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 3].length) (baseStart_6760011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760011 prefixEnd_6760011 := by exact prefixLift 6760011
  have htrace : WordTrace (prefixWord ++ tailWord_6760011) baseStart_6760011 baseEnd_6760011 := by
    simpa [prefixWord, tailWord_6760011, baseEnd_6760011] using wordTrace_append hprefix tailTrace_6760011
  have hstable : (prefixWord ++ tailWord_6760011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760011).length < 2 ^ (prefixWord ++ tailWord_6760011).sum := by decide
  have hdescent : baseEnd_6760011 < baseStart_6760011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760031 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 7, 5]
def baseStart_6760031 : Nat := 118140960795 + 6760031 * 2 ^ 59
def prefixEnd_6760031 : Nat := 4983230072969 + 3 ^ 40 * 6760031 * 2
def baseEnd_6760031 : Nat := 1157048380764648693774563

theorem tailTrace_6760031 : CollatzResearch.WordTrace tailWord_6760031 prefixEnd_6760031 1157048380764648693774563 := by
  unfold tailWord_6760031
  simp only [CollatzResearch.WordTrace]
  refine ⟨246558586172569683223767947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164372390781713122149178631 246558586172569683223767947)
  ·
    refine ⟨369837879258854524835651921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246558586172569683223767947 369837879258854524835651921)
    ·
      refine ⟨277378409444140893626738941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369837879258854524835651921 277378409444140893626738941)
      ·
        refine ⟨104016903541552835110027103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277378409444140893626738941 104016903541552835110027103)
        ·
          refine ⟨156025355312329252665040655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104016903541552835110027103 156025355312329252665040655)
          ·
            refine ⟨234038032968493878997560983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156025355312329252665040655 234038032968493878997560983)
            ·
              refine ⟨351057049452740818496341475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234038032968493878997560983 351057049452740818496341475)
              ·
                refine ⟨526585574179111227744512213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351057049452740818496341475 526585574179111227744512213)
                ·
                  refine ⟨12341849394822919400262005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 526585574179111227744512213 12341849394822919400262005)
                  ·
                    refine ⟨1157048380764648693774563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12341849394822919400262005 1157048380764648693774563)
                    ·
                      rfl

theorem cell23_6760031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_6760031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760031 prefixEnd_6760031 := by exact prefixLift 6760031
  have htrace : WordTrace (prefixWord ++ tailWord_6760031) baseStart_6760031 baseEnd_6760031 := by
    simpa [prefixWord, tailWord_6760031, baseEnd_6760031] using wordTrace_append hprefix tailTrace_6760031
  have hstable : (prefixWord ++ tailWord_6760031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760031).length < 2 ^ (prefixWord ++ tailWord_6760031).sum := by decide
  have hdescent : baseEnd_6760031 < baseStart_6760031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760065 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 1, 5]
def baseStart_6760065 : Nat := 118140960795 + 6760065 * 2 ^ 59
def prefixEnd_6760065 : Nat := 4983230072969 + 3 ^ 40 * 6760065 * 2
def baseEnd_6760065 : Nat := 1157054200212066316099511

theorem tailTrace_6760065 : CollatzResearch.WordTrace tailWord_6760065 prefixEnd_6760065 1157054200212066316099511 := by
  unfold tailWord_6760065
  simp only [CollatzResearch.WordTrace]
  refine ⟨246559826254446507030505649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164373217502964338020337099 246559826254446507030505649)
  ·
    refine ⟨184919869690834880272879237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246559826254446507030505649 184919869690834880272879237)
    ·
      refine ⟨34672475567031540051164857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184919869690834880272879237 34672475567031540051164857)
      ·
        refine ⟨26004356675273655038373643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34672475567031540051164857 26004356675273655038373643)
        ·
          refine ⟨39006535012910482557560465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26004356675273655038373643 39006535012910482557560465)
          ·
            refine ⟨29254901259682861918170349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39006535012910482557560465 29254901259682861918170349)
            ·
              refine ⟨10970587972381073219313881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29254901259682861918170349 10970587972381073219313881)
              ·
                refine ⟨8227940979285804914485411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10970587972381073219313881 8227940979285804914485411)
                ·
                  refine ⟨12341911468928707371728117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8227940979285804914485411 12341911468928707371728117)
                  ·
                    refine ⟨1157054200212066316099511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12341911468928707371728117 1157054200212066316099511)
                    ·
                      rfl

theorem cell23_6760065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_6760065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760065 prefixEnd_6760065 := by exact prefixLift 6760065
  have htrace : WordTrace (prefixWord ++ tailWord_6760065) baseStart_6760065 baseEnd_6760065 := by
    simpa [prefixWord, tailWord_6760065, baseEnd_6760065] using wordTrace_append hprefix tailTrace_6760065
  have hstable : (prefixWord ++ tailWord_6760065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760065).length < 2 ^ (prefixWord ++ tailWord_6760065).sum := by decide
  have hdescent : baseEnd_6760065 < baseStart_6760065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760078 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_6760078 : Nat := 118140960795 + 6760078 * 2 ^ 59
def prefixEnd_6760078 : Nat := 4983230072969 + 3 ^ 40 * 6760078 * 2
def baseEnd_6760078 : Nat := 1157056425294902465811991

theorem tailTrace_6760078 : CollatzResearch.WordTrace tailWord_6760078 prefixEnd_6760078 1157056425294902465811991 := by
  unfold tailWord_6760078
  simp only [CollatzResearch.WordTrace]
  refine ⟨30820037550424926281341111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164373533602266273500485925 30820037550424926281341111)
  ·
    refine ⟨46230056325637389422011667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30820037550424926281341111 46230056325637389422011667)
    ·
      refine ⟨69345084488456084133017501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46230056325637389422011667 69345084488456084133017501)
      ·
        refine ⟨26004406683171031549881563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69345084488456084133017501 26004406683171031549881563)
        ·
          refine ⟨39006610024756547324822345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26004406683171031549881563 39006610024756547324822345)
          ·
            refine ⟨29254957518567410493616759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39006610024756547324822345 29254957518567410493616759)
            ·
              refine ⟨43882436277851115740425139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29254957518567410493616759 43882436277851115740425139)
              ·
                refine ⟨65823654416776673610637709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43882436277851115740425139 65823654416776673610637709)
                ·
                  refine ⟨24683870406291252603989141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65823654416776673610637709 24683870406291252603989141)
                  ·
                    refine ⟨1157056425294902465811991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24683870406291252603989141 1157056425294902465811991)
                    ·
                      rfl

theorem cell23_6760078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_6760078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760078 prefixEnd_6760078 := by exact prefixLift 6760078
  have htrace : WordTrace (prefixWord ++ tailWord_6760078) baseStart_6760078 baseEnd_6760078 := by
    simpa [prefixWord, tailWord_6760078, baseEnd_6760078] using wordTrace_append hprefix tailTrace_6760078
  have hstable : (prefixWord ++ tailWord_6760078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760078).length < 2 ^ (prefixWord ++ tailWord_6760078).sum := by decide
  have hdescent : baseEnd_6760078 < baseStart_6760078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760081 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_6760081 : Nat := 118140960795 + 6760081 * 2 ^ 59
def prefixEnd_6760081 : Nat := 4983230072969 + 3 ^ 40 * 6760081 * 2
def baseEnd_6760081 : Nat := 3471170816326670885698459

theorem tailTrace_6760081 : CollatzResearch.WordTrace tailWord_6760081 prefixEnd_6760081 3471170816326670885698459 := by
  unfold tailWord_6760081
  simp only [CollatzResearch.WordTrace]
  refine ⟨246560409822388541763088097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164373606548259027842058731 246560409822388541763088097)
  ·
    refine ⟨184920307366791406322316073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246560409822388541763088097 184920307366791406322316073)
    ·
      refine ⟨138690230525093554741737055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184920307366791406322316073 138690230525093554741737055)
      ·
        refine ⟨208035345787640332112605583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138690230525093554741737055 208035345787640332112605583)
        ·
          refine ⟨312053018681460498168908375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208035345787640332112605583 312053018681460498168908375)
          ·
            refine ⟨468079528022190747253362563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312053018681460498168908375 468079528022190747253362563)
            ·
              refine ⟨702119292033286120880043845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468079528022190747253362563 702119292033286120880043845)
              ·
                refine ⟨131647367256241147665008221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702119292033286120880043845 131647367256241147665008221)
                ·
                  refine ⟨49367762721090430374378083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131647367256241147665008221 49367762721090430374378083)
                  ·
                    refine ⟨74051644081635645561567125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49367762721090430374378083 74051644081635645561567125)
                    ·
                      refine ⟨3471170816326670885698459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74051644081635645561567125 3471170816326670885698459)
                      ·
                        rfl

theorem cell23_6760081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_6760081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760081 prefixEnd_6760081 := by exact prefixLift 6760081
  have htrace : WordTrace (prefixWord ++ tailWord_6760081) baseStart_6760081 baseEnd_6760081 := by
    simpa [prefixWord, tailWord_6760081, baseEnd_6760081] using wordTrace_append hprefix tailTrace_6760081
  have hstable : (prefixWord ++ tailWord_6760081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760081).length < 2 ^ (prefixWord ++ tailWord_6760081).sum := by decide
  have hdescent : baseEnd_6760081 < baseStart_6760081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760096 : List Nat := [2, 1, 1, 4, 3, 3, 2, 2, 1, 1, 3]
def baseStart_6760096 : Nat := 118140960795 + 6760096 * 2 ^ 59
def prefixEnd_6760096 : Nat := 4983230072969 + 3 ^ 40 * 6760096 * 2
def baseEnd_6760096 : Nat := 3471178518536488327010891

theorem tailTrace_6760096 : CollatzResearch.WordTrace tailWord_6760096 prefixEnd_6760096 3471178518536488327010891 := by
  unfold tailWord_6760096
  simp only [CollatzResearch.WordTrace]
  refine ⟨123280478458667099662442071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164373971278222799549922761 123280478458667099662442071)
  ·
    refine ⟨184920717688000649493663107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123280478458667099662442071 184920717688000649493663107)
    ·
      refine ⟨277381076532000974240494661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184920717688000649493663107 277381076532000974240494661)
      ·
        refine ⟨52008951849750182670092749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277381076532000974240494661 52008951849750182670092749)
        ·
          refine ⟨19503356943656318501284781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52008951849750182670092749 19503356943656318501284781)
          ·
            refine ⟨7313758853871119437981793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19503356943656318501284781 7313758853871119437981793)
            ·
              refine ⟨5485319140403339578486345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7313758853871119437981793 5485319140403339578486345)
              ·
                refine ⟨4113989355302504683864759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5485319140403339578486345 4113989355302504683864759)
                ·
                  refine ⟨6170984032953757025797139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113989355302504683864759 6170984032953757025797139)
                  ·
                    refine ⟨9256476049430635538695709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6170984032953757025797139 9256476049430635538695709)
                    ·
                      refine ⟨3471178518536488327010891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9256476049430635538695709 3471178518536488327010891)
                      ·
                        rfl

theorem cell23_6760096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_6760096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760096 prefixEnd_6760096 := by exact prefixLift 6760096
  have htrace : WordTrace (prefixWord ++ tailWord_6760096) baseStart_6760096 baseEnd_6760096 := by
    simpa [prefixWord, tailWord_6760096, baseEnd_6760096] using wordTrace_append hprefix tailTrace_6760096
  have hstable : (prefixWord ++ tailWord_6760096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760096).length < 2 ^ (prefixWord ++ tailWord_6760096).sum := by decide
  have hdescent : baseEnd_6760096 < baseStart_6760096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760130 : List Nat := [3, 5, 1, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_6760130 : Nat := 118140960795 + 6760130 * 2 ^ 59
def prefixEnd_6760130 : Nat := 4983230072969 + 3 ^ 40 * 6760130 * 2
def baseEnd_6760130 : Nat := 3471195976878741193985735

theorem tailTrace_6760130 : CollatzResearch.WordTrace tailWord_6760130 prefixEnd_6760130 3471195976878741193985735 := by
  unfold tailWord_6760130
  simp only [CollatzResearch.WordTrace]
  refine ⟨61640549249802755782905461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164374797999474015421081229 61640549249802755782905461)
  ·
    refine ⟨5778801492169008354647387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61640549249802755782905461 5778801492169008354647387)
    ·
      refine ⟨8668202238253512531971081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778801492169008354647387 8668202238253512531971081)
      ·
        refine ⟨6501151678690134398978311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8668202238253512531971081 6501151678690134398978311)
        ·
          refine ⟨9751727518035201598467467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6501151678690134398978311 9751727518035201598467467)
          ·
            refine ⟨14627591277052802397701201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9751727518035201598467467 14627591277052802397701201)
            ·
              refine ⟨10970693457789601798275901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14627591277052802397701201 10970693457789601798275901)
              ·
                refine ⟨4114010046671100674353463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10970693457789601798275901 4114010046671100674353463)
                ·
                  refine ⟨6171015070006651011530195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114010046671100674353463 6171015070006651011530195)
                  ·
                    refine ⟨9256522605009976517295293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6171015070006651011530195 9256522605009976517295293)
                    ·
                      refine ⟨3471195976878741193985735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9256522605009976517295293 3471195976878741193985735)
                      ·
                        rfl

theorem cell23_6760130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_6760130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760130 prefixEnd_6760130 := by exact prefixLift 6760130
  have htrace : WordTrace (prefixWord ++ tailWord_6760130) baseStart_6760130 baseEnd_6760130 := by
    simpa [prefixWord, tailWord_6760130, baseEnd_6760130] using wordTrace_append hprefix tailTrace_6760130
  have hstable : (prefixWord ++ tailWord_6760130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760130).length < 2 ^ (prefixWord ++ tailWord_6760130).sum := by decide
  have hdescent : baseEnd_6760130 < baseStart_6760130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760135 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_6760135 : Nat := 118140960795 + 6760135 * 2 ^ 59
def prefixEnd_6760135 : Nat := 4983230072969 + 3 ^ 40 * 6760135 * 2
def baseEnd_6760135 : Nat := 3471198544282013674423211

theorem tailTrace_6760135 : CollatzResearch.WordTrace tailWord_6760135 prefixEnd_6760135 3471198544282013674423211 := by
  unfold tailWord_6760135
  simp only [CollatzResearch.WordTrace]
  refine ⟨246562379364192908985553859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164374919576128605990369239 246562379364192908985553859)
  ·
    refine ⟨369843569046289363478330789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246562379364192908985553859 369843569046289363478330789)
    ·
      refine ⟨69345669196179255652187023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369843569046289363478330789 69345669196179255652187023)
      ·
        refine ⟨104018503794268883478280535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69345669196179255652187023 104018503794268883478280535)
        ·
          refine ⟨156027755691403325217420803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104018503794268883478280535 156027755691403325217420803)
          ·
            refine ⟨234041633537104987826131205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156027755691403325217420803 234041633537104987826131205)
            ·
              refine ⟨43882806288207185217399601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234041633537104987826131205 43882806288207185217399601)
              ·
                refine ⟨32912104716155388913049701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43882806288207185217399601 32912104716155388913049701)
                ·
                  refine ⟨6171019634279135421196819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32912104716155388913049701 6171019634279135421196819)
                  ·
                    refine ⟨9256529451418703131795229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6171019634279135421196819 9256529451418703131795229)
                    ·
                      refine ⟨3471198544282013674423211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9256529451418703131795229 3471198544282013674423211)
                      ·
                        rfl

theorem cell23_6760135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_6760135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760135 prefixEnd_6760135 := by exact prefixLift 6760135
  have htrace : WordTrace (prefixWord ++ tailWord_6760135) baseStart_6760135 baseEnd_6760135 := by
    simpa [prefixWord, tailWord_6760135, baseEnd_6760135] using wordTrace_append hprefix tailTrace_6760135
  have hstable : (prefixWord ++ tailWord_6760135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760135).length < 2 ^ (prefixWord ++ tailWord_6760135).sum := by decide
  have hdescent : baseEnd_6760135 < baseStart_6760135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760215 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 7]
def baseStart_6760215 : Nat := 118140960795 + 6760215 * 2 ^ 59
def prefixEnd_6760215 : Nat := 4983230072969 + 3 ^ 40 * 6760215 * 2
def baseEnd_6760215 : Nat := 385693291414930373491427

theorem tailTrace_6760215 : CollatzResearch.WordTrace tailWord_6760215 prefixEnd_6760215 385693291414930373491427 := by
  unfold tailWord_6760215
  simp only [CollatzResearch.WordTrace]
  refine ⟨246565297203903082648466099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164376864802602055098977399 246565297203903082648466099)
  ·
    refine ⟨369847945805854623972699149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246565297203903082648466099 369847945805854623972699149)
    ·
      refine ⟨138692979677195483989762181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369847945805854623972699149 138692979677195483989762181)
      ·
        refine ⟨26004933689474153248080409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138692979677195483989762181 26004933689474153248080409)
        ·
          refine ⟨19503700267105614936060307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26004933689474153248080409 19503700267105614936060307)
          ·
            refine ⟨29255550400658422404090461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19503700267105614936060307 29255550400658422404090461)
            ·
              refine ⟨10970831400246908401533923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29255550400658422404090461 10970831400246908401533923)
              ·
                refine ⟨16456247100370362602300885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10970831400246908401533923 16456247100370362602300885)
                ·
                  refine ⟨385693291414930373491427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16456247100370362602300885 385693291414930373491427)
                  ·
                    rfl

theorem cell23_6760215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 7].length) (baseStart_6760215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760215 prefixEnd_6760215 := by exact prefixLift 6760215
  have htrace : WordTrace (prefixWord ++ tailWord_6760215) baseStart_6760215 baseEnd_6760215 := by
    simpa [prefixWord, tailWord_6760215, baseEnd_6760215] using wordTrace_append hprefix tailTrace_6760215
  have hstable : (prefixWord ++ tailWord_6760215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760215).length < 2 ^ (prefixWord ++ tailWord_6760215).sum := by decide
  have hdescent : baseEnd_6760215 < baseStart_6760215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760265 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_6760265 : Nat := 118140960795 + 6760265 * 2 ^ 59
def prefixEnd_6760265 : Nat := 4983230072969 + 3 ^ 40 * 6760265 * 2
def baseEnd_6760265 : Nat := 3471265296767098165797613

theorem tailTrace_6760265 : CollatzResearch.WordTrace tailWord_6760265 prefixEnd_6760265 3471265296767098165797613 := by
  unfold tailWord_6760265
  simp only [CollatzResearch.WordTrace]
  refine ⟨246567120853721941187786249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164378080569147960791857499 246567120853721941187786249)
  ·
    refine ⟨184925340640291455890839687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246567120853721941187786249 184925340640291455890839687)
    ·
      refine ⟨277388010960437183836259531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184925340640291455890839687 277388010960437183836259531)
      ·
        refine ⟨416082016440655775754389297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277388010960437183836259531 416082016440655775754389297)
        ·
          refine ⟨312061512330491831815791973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416082016440655775754389297 312061512330491831815791973)
          ·
            refine ⟨58511533561967218465460995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312061512330491831815791973 58511533561967218465460995)
            ·
              refine ⟨87767300342950827698191493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58511533561967218465460995 87767300342950827698191493)
              ·
                refine ⟨16456368814303280193410905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87767300342950827698191493 16456368814303280193410905)
                ·
                  refine ⟨12342276610727460145058179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16456368814303280193410905 12342276610727460145058179)
                  ·
                    refine ⟨18513414916091190217587269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12342276610727460145058179 18513414916091190217587269)
                    ·
                      refine ⟨3471265296767098165797613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18513414916091190217587269 3471265296767098165797613)
                      ·
                        rfl

theorem cell23_6760265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_6760265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760265 prefixEnd_6760265 := by exact prefixLift 6760265
  have htrace : WordTrace (prefixWord ++ tailWord_6760265) baseStart_6760265 baseEnd_6760265 := by
    simpa [prefixWord, tailWord_6760265, baseEnd_6760265] using wordTrace_append hprefix tailTrace_6760265
  have hstable : (prefixWord ++ tailWord_6760265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760265).length < 2 ^ (prefixWord ++ tailWord_6760265).sum := by decide
  have hdescent : baseEnd_6760265 < baseStart_6760265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760269 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_6760269 : Nat := 118140960795 + 6760269 * 2 ^ 59
def prefixEnd_6760269 : Nat := 4983230072969 + 3 ^ 40 * 6760269 * 2
def baseEnd_6760269 : Nat := 3471267350689716150147595

theorem tailTrace_6760269 : CollatzResearch.WordTrace tailWord_6760269 prefixEnd_6760269 3471267350689716150147595 := by
  unfold tailWord_6760269
  simp only [CollatzResearch.WordTrace]
  refine ⟨246567266745707449870931861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164378177830471633247287907 246567266745707449870931861)
  ·
    refine ⟨11557840628705036712699931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 246567266745707449870931861 11557840628705036712699931)
    ·
      refine ⟨17336760943057555069049897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11557840628705036712699931 17336760943057555069049897)
      ·
        refine ⟨13002570707293166301787423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17336760943057555069049897 13002570707293166301787423)
        ·
          refine ⟨19503856060939749452681135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13002570707293166301787423 19503856060939749452681135)
          ·
            refine ⟨29255784091409624179021703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19503856060939749452681135 29255784091409624179021703)
            ·
              refine ⟨43883676137114436268532555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29255784091409624179021703 43883676137114436268532555)
              ·
                refine ⟨65825514205671654402798833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43883676137114436268532555 65825514205671654402798833)
                ·
                  refine ⟨49369135654253740802099125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65825514205671654402798833 49369135654253740802099125)
                  ·
                    refine ⟨4628356467586288200196793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49369135654253740802099125 4628356467586288200196793)
                    ·
                      refine ⟨3471267350689716150147595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628356467586288200196793 3471267350689716150147595)
                      ·
                        rfl

theorem cell23_6760269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_6760269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760269 prefixEnd_6760269 := by exact prefixLift 6760269
  have htrace : WordTrace (prefixWord ++ tailWord_6760269) baseStart_6760269 baseEnd_6760269 := by
    simpa [prefixWord, tailWord_6760269, baseEnd_6760269] using wordTrace_append hprefix tailTrace_6760269
  have hstable : (prefixWord ++ tailWord_6760269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760269).length < 2 ^ (prefixWord ++ tailWord_6760269).sum := by decide
  have hdescent : baseEnd_6760269 < baseStart_6760269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760282 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2]
def baseStart_6760282 : Nat := 118140960795 + 6760282 * 2 ^ 59
def prefixEnd_6760282 : Nat := 4983230072969 + 3 ^ 40 * 6760282 * 2
def baseEnd_6760282 : Nat := 3471274025938224599285035

theorem tailTrace_6760282 : CollatzResearch.WordTrace tailWord_6760282 prefixEnd_6760282 3471274025938224599285035 := by
  unfold tailWord_6760282
  simp only [CollatzResearch.WordTrace]
  refine ⟨61641935223665088272788775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164378493929773568727436733 61641935223665088272788775)
  ·
    refine ⟨92462902835497632409183163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61641935223665088272788775 92462902835497632409183163)
    ·
      refine ⟨138694354253246448613774745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92462902835497632409183163 138694354253246448613774745)
      ·
        refine ⟨104020765689934836460331059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138694354253246448613774745 104020765689934836460331059)
        ·
          refine ⟨156031148534902254690496589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104020765689934836460331059 156031148534902254690496589)
          ·
            refine ⟨58511680700588345508936221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156031148534902254690496589 58511680700588345508936221)
            ·
              refine ⟨21941880262720629565851083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58511680700588345508936221 21941880262720629565851083)
              ·
                refine ⟨32912820394080944348776625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21941880262720629565851083 32912820394080944348776625)
                ·
                  refine ⟨24684615295560708261582469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32912820394080944348776625 24684615295560708261582469)
                  ·
                    refine ⟨4628365367917632799046713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24684615295560708261582469 4628365367917632799046713)
                    ·
                      refine ⟨3471274025938224599285035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628365367917632799046713 3471274025938224599285035)
                      ·
                        rfl

theorem cell23_6760282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_6760282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760282 prefixEnd_6760282 := by exact prefixLift 6760282
  have htrace : WordTrace (prefixWord ++ tailWord_6760282) baseStart_6760282 baseEnd_6760282 := by
    simpa [prefixWord, tailWord_6760282, baseEnd_6760282] using wordTrace_append hprefix tailTrace_6760282
  have hstable : (prefixWord ++ tailWord_6760282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760282).length < 2 ^ (prefixWord ++ tailWord_6760282).sum := by decide
  have hdescent : baseEnd_6760282 < baseStart_6760282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760349 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_6760349 : Nat := 118140960795 + 6760349 * 2 ^ 59
def prefixEnd_6760349 : Nat := 4983230072969 + 3 ^ 40 * 6760349 * 2
def baseEnd_6760349 : Nat := 3471308429142075837147227

theorem tailTrace_6760349 : CollatzResearch.WordTrace tailWord_6760349 prefixEnd_6760349 3471308429142075837147227 := by
  unfold tailWord_6760349
  simp only [CollatzResearch.WordTrace]
  refine ⟨246570184585417623533844101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164380123056945082355896067 246570184585417623533844101)
  ·
    refine ⟨46231909609765804412595769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246570184585417623533844101 46231909609765804412595769)
    ·
      refine ⟨34673932207324353309446827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46231909609765804412595769 34673932207324353309446827)
      ·
        refine ⟨52010898310986529964170241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34673932207324353309446827 52010898310986529964170241)
        ·
          refine ⟨39008173733239897473127681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52010898310986529964170241 39008173733239897473127681)
          ·
            refine ⟨29256130299929923104845761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39008173733239897473127681 29256130299929923104845761)
            ·
              refine ⟨21942097724947442328634321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29256130299929923104845761 21942097724947442328634321)
              ·
                refine ⟨16456573293710581746475741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21942097724947442328634321 16456573293710581746475741)
                ·
                  refine ⟨6171214985141468154928403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16456573293710581746475741 6171214985141468154928403)
                  ·
                    refine ⟨9256822477712202232392605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6171214985141468154928403 9256822477712202232392605)
                    ·
                      refine ⟨3471308429142075837147227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9256822477712202232392605 3471308429142075837147227)
                      ·
                        rfl

theorem cell23_6760349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_6760349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760349 prefixEnd_6760349 := by exact prefixLift 6760349
  have htrace : WordTrace (prefixWord ++ tailWord_6760349) baseStart_6760349 baseEnd_6760349 := by
    simpa [prefixWord, tailWord_6760349, baseEnd_6760349] using wordTrace_append hprefix tailTrace_6760349
  have hstable : (prefixWord ++ tailWord_6760349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760349).length < 2 ^ (prefixWord ++ tailWord_6760349).sum := by decide
  have hdescent : baseEnd_6760349 < baseStart_6760349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760359 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_6760359 : Nat := 118140960795 + 6760359 * 2 ^ 59
def prefixEnd_6760359 : Nat := 4983230072969 + 3 ^ 40 * 6760359 * 2
def baseEnd_6760359 : Nat := 3471313563948620798022181

theorem tailTrace_6760359 : CollatzResearch.WordTrace tailWord_6760359 prefixEnd_6760359 3471313563948620798022181 := by
  unfold tailWord_6760359
  simp only [CollatzResearch.WordTrace]
  refine ⟨246570549315381395241708131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164380366210254263494472087 246570549315381395241708131)
  ·
    refine ⟨369855823973072092862562197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246570549315381395241708131 369855823973072092862562197)
    ·
      refine ⟨17336991748737754352932603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 369855823973072092862562197 17336991748737754352932603)
      ·
        refine ⟨26005487623106631529398905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17336991748737754352932603 26005487623106631529398905)
        ·
          refine ⟨19504115717329973647049179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26005487623106631529398905 19504115717329973647049179)
          ·
            refine ⟨29256173575994960470573769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19504115717329973647049179 29256173575994960470573769)
            ·
              refine ⟨21942130181996220352930327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29256173575994960470573769 21942130181996220352930327)
              ·
                refine ⟨32913195272994330529395491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21942130181996220352930327 32913195272994330529395491)
                ·
                  refine ⟨49369792909491495794093237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32913195272994330529395491 49369792909491495794093237)
                  ·
                    refine ⟨4628418085264827730696241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49369792909491495794093237 4628418085264827730696241)
                    ·
                      refine ⟨3471313563948620798022181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628418085264827730696241 3471313563948620798022181)
                      ·
                        rfl

theorem cell23_6760359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_6760359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760359 prefixEnd_6760359 := by exact prefixLift 6760359
  have htrace : WordTrace (prefixWord ++ tailWord_6760359) baseStart_6760359 baseEnd_6760359 := by
    simpa [prefixWord, tailWord_6760359, baseEnd_6760359] using wordTrace_append hprefix tailTrace_6760359
  have hstable : (prefixWord ++ tailWord_6760359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760359).length < 2 ^ (prefixWord ++ tailWord_6760359).sum := by decide
  have hdescent : baseEnd_6760359 < baseStart_6760359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760360 : List Nat := [2, 1, 6, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6760360 : Nat := 118140960795 + 6760360 * 2 ^ 59
def prefixEnd_6760360 : Nat := 4983230072969 + 3 ^ 40 * 6760360 * 2
def baseEnd_6760360 : Nat := 1157104692476425098036559

theorem tailTrace_6760360 : CollatzResearch.WordTrace tailWord_6760360 prefixEnd_6760360 1157104692476425098036559 := by
  unfold tailWord_6760360
  simp only [CollatzResearch.WordTrace]
  refine ⟨123285292894188886206247267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164380390525585181608329689 123285292894188886206247267)
  ·
    refine ⟨184927939341283329309370901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123285292894188886206247267 184927939341283329309370901)
    ·
      refine ⟨8668497156622656061376761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184927939341283329309370901 8668497156622656061376761)
      ·
        refine ⟨6501372867466992046032571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8668497156622656061376761 6501372867466992046032571)
        ·
          refine ⟨9752059301200488069048857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6501372867466992046032571 9752059301200488069048857)
          ·
            refine ⟨7314044475900366051786643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9752059301200488069048857 7314044475900366051786643)
            ·
              refine ⟨10971066713850549077679965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7314044475900366051786643 10971066713850549077679965)
              ·
                refine ⟨4114150017693955904129987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10971066713850549077679965 4114150017693955904129987)
                ·
                  refine ⟨6171225026540933856194981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114150017693955904129987 6171225026540933856194981)
                  ·
                    refine ⟨1157104692476425098036559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6171225026540933856194981 1157104692476425098036559)
                    ·
                      rfl

theorem cell23_6760360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6760360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760360 prefixEnd_6760360 := by exact prefixLift 6760360
  have htrace : WordTrace (prefixWord ++ tailWord_6760360) baseStart_6760360 baseEnd_6760360 := by
    simpa [prefixWord, tailWord_6760360, baseEnd_6760360] using wordTrace_append hprefix tailTrace_6760360
  have hstable : (prefixWord ++ tailWord_6760360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760360).length < 2 ^ (prefixWord ++ tailWord_6760360).sum := by decide
  have hdescent : baseEnd_6760360 < baseStart_6760360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760389 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 3, 2, 2]
def baseStart_6760389 : Nat := 118140960795 + 6760389 * 2 ^ 59
def prefixEnd_6760389 : Nat := 4983230072969 + 3 ^ 40 * 6760389 * 2
def baseEnd_6760389 : Nat := 3471328968368255680647043

theorem tailTrace_6760389 : CollatzResearch.WordTrace tailWord_6760389 prefixEnd_6760389 3471328968368255680647043 := by
  unfold tailWord_6760389
  simp only [CollatzResearch.WordTrace]
  refine ⟨246571643505272710365300221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164381095670181806910200147 246571643505272710365300221)
  ·
    refine ⟨92464366314477266386987583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246571643505272710365300221 92464366314477266386987583)
    ·
      refine ⟨138696549471715899580481375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92464366314477266386987583 138696549471715899580481375)
      ·
        refine ⟨208044824207573849370722063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138696549471715899580481375 208044824207573849370722063)
        ·
          refine ⟨312067236311360774056083095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208044824207573849370722063 312067236311360774056083095)
          ·
            refine ⟨468100854467041161084124643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312067236311360774056083095 468100854467041161084124643)
            ·
              refine ⟨702151281700561741626186965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468100854467041161084124643 702151281700561741626186965)
              ·
                refine ⟨16456670664856915819363757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 702151281700561741626186965 16456670664856915819363757)
                ·
                  refine ⟨6171251499321343432261409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16456670664856915819363757 6171251499321343432261409)
                  ·
                    refine ⟨4628438624491007574196057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6171251499321343432261409 4628438624491007574196057)
                    ·
                      refine ⟨3471328968368255680647043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628438624491007574196057 3471328968368255680647043)
                      ·
                        rfl

theorem cell23_6760389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_6760389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760389 prefixEnd_6760389 := by exact prefixLift 6760389
  have htrace : WordTrace (prefixWord ++ tailWord_6760389) baseStart_6760389 baseEnd_6760389 := by
    simpa [prefixWord, tailWord_6760389, baseEnd_6760389] using wordTrace_append hprefix tailTrace_6760389
  have hstable : (prefixWord ++ tailWord_6760389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760389).length < 2 ^ (prefixWord ++ tailWord_6760389).sum := by decide
  have hdescent : baseEnd_6760389 < baseStart_6760389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760392 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_6760392 : Nat := 118140960795 + 6760392 * 2 ^ 59
def prefixEnd_6760392 : Nat := 4983230072969 + 3 ^ 40 * 6760392 * 2
def baseEnd_6760392 : Nat := 3471330508810219168909529

theorem tailTrace_6760392 : CollatzResearch.WordTrace tailWord_6760392 prefixEnd_6760392 3471330508810219168909529 := by
  unfold tailWord_6760392
  simp only [CollatzResearch.WordTrace]
  refine ⟨123285876462130920938829715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164381168616174561251772953 123285876462130920938829715)
  ·
    refine ⟨184928814693196381408244573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123285876462130920938829715 184928814693196381408244573)
    ·
      refine ⟨69348305509948643028091715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184928814693196381408244573 69348305509948643028091715)
      ·
        refine ⟨104022458264922964542137573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69348305509948643028091715 104022458264922964542137573)
        ·
          refine ⟨19504210924673055851650795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104022458264922964542137573 19504210924673055851650795)
          ·
            refine ⟨29256316387009583777476193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19504210924673055851650795 29256316387009583777476193)
            ·
              refine ⟨21942237290257187833107145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29256316387009583777476193 21942237290257187833107145)
              ·
                refine ⟨16456677967692890874830359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21942237290257187833107145 16456677967692890874830359)
                ·
                  refine ⟨24685016951539336312245539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16456677967692890874830359 24685016951539336312245539)
                  ·
                    refine ⟨37027525427309004468368309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24685016951539336312245539 37027525427309004468368309)
                    ·
                      refine ⟨3471330508810219168909529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37027525427309004468368309 3471330508810219168909529)
                      ·
                        rfl

theorem cell23_6760392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_6760392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760392 prefixEnd_6760392 := by exact prefixLift 6760392
  have htrace : WordTrace (prefixWord ++ tailWord_6760392) baseStart_6760392 baseEnd_6760392 := by
    simpa [prefixWord, tailWord_6760392, baseEnd_6760392] using wordTrace_append hprefix tailTrace_6760392
  have hstable : (prefixWord ++ tailWord_6760392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760392).length < 2 ^ (prefixWord ++ tailWord_6760392).sum := by decide
  have hdescent : baseEnd_6760392 < baseStart_6760392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760395 : List Nat := [1, 1, 1, 1, 3, 4, 4, 8]
def baseStart_6760395 : Nat := 118140960795 + 6760395 * 2 ^ 59
def prefixEnd_6760395 : Nat := 4983230072969 + 3 ^ 40 * 6760395 * 2
def baseEnd_6760395 : Nat := 128567853676006765080445

theorem tailTrace_6760395 : CollatzResearch.WordTrace tailWord_6760395 prefixEnd_6760395 128567853676006765080445 := by
  unfold tailWord_6760395
  simp only [CollatzResearch.WordTrace]
  refine ⟨246571862343250973390018639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164381241562167315593345759 246571862343250973390018639)
  ·
    refine ⟨369857793514876460085027959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246571862343250973390018639 369857793514876460085027959)
    ·
      refine ⟨554786690272314690127541939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369857793514876460085027959 554786690272314690127541939)
      ·
        refine ⟨832180035408472035191312909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554786690272314690127541939 832180035408472035191312909)
        ·
          refine ⟨312067513278177013196742341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 832180035408472035191312909 312067513278177013196742341)
          ·
            refine ⟨58512658739658189974389189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312067513278177013196742341 58512658739658189974389189)
            ·
              refine ⟨10971123513685910620197973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58512658739658189974389189 10971123513685910620197973)
              ·
                refine ⟨128567853676006765080445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10971123513685910620197973 128567853676006765080445)
                ·
                  rfl

theorem cell23_6760395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 8].length) (baseStart_6760395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760395 prefixEnd_6760395 := by exact prefixLift 6760395
  have htrace : WordTrace (prefixWord ++ tailWord_6760395) baseStart_6760395 baseEnd_6760395 := by
    simpa [prefixWord, tailWord_6760395, baseEnd_6760395] using wordTrace_append hprefix tailTrace_6760395
  have hstable : (prefixWord ++ tailWord_6760395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760395).length < 2 ^ (prefixWord ++ tailWord_6760395).sum := by decide
  have hdescent : baseEnd_6760395 < baseStart_6760395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760406 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_6760406 : Nat := 118140960795 + 6760406 * 2 ^ 59
def prefixEnd_6760406 : Nat := 4983230072969 + 3 ^ 40 * 6760406 * 2
def baseEnd_6760406 : Nat := 3471337697539382114134465

theorem tailTrace_6760406 : CollatzResearch.WordTrace tailWord_6760406 prefixEnd_6760406 3471337697539382114134465 := by
  unfold tailWord_6760406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15410766471638195141791817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164381509030807414845779381 15410766471638195141791817)
  ·
    refine ⟨11558074853728646356343863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15410766471638195141791817 11558074853728646356343863)
    ·
      refine ⟨17337112280592969534515795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11558074853728646356343863 17337112280592969534515795)
      ·
        refine ⟨26005668420889454301773693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17337112280592969534515795 26005668420889454301773693)
        ·
          refine ⟨9752125657833545363165135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26005668420889454301773693 9752125657833545363165135)
          ·
            refine ⟨14628188486750318044747703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9752125657833545363165135 14628188486750318044747703)
            ·
              refine ⟨21942282730125477067121555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14628188486750318044747703 21942282730125477067121555)
              ·
                refine ⟨32913424095188215600682333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21942282730125477067121555 32913424095188215600682333)
                ·
                  refine ⟨12342534035695580850255875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32913424095188215600682333 12342534035695580850255875)
                  ·
                    refine ⟨18513801053543371275383813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12342534035695580850255875 18513801053543371275383813)
                    ·
                      refine ⟨3471337697539382114134465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18513801053543371275383813 3471337697539382114134465)
                      ·
                        rfl

theorem cell23_6760406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_6760406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760406 prefixEnd_6760406 := by exact prefixLift 6760406
  have htrace : WordTrace (prefixWord ++ tailWord_6760406) baseStart_6760406 baseEnd_6760406 := by
    simpa [prefixWord, tailWord_6760406, baseEnd_6760406] using wordTrace_append hprefix tailTrace_6760406
  have hstable : (prefixWord ++ tailWord_6760406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760406).length < 2 ^ (prefixWord ++ tailWord_6760406).sum := by decide
  have hdescent : baseEnd_6760406 < baseStart_6760406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760409 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 3]
def baseStart_6760409 : Nat := 118140960795 + 6760409 * 2 ^ 59
def prefixEnd_6760409 : Nat := 4983230072969 + 3 ^ 40 * 6760409 * 2
def baseEnd_6760409 : Nat := 3471339237981345602396951

theorem tailTrace_6760409 : CollatzResearch.WordTrace tailWord_6760409 prefixEnd_6760409 3471339237981345602396951 := by
  unfold tailWord_6760409
  simp only [CollatzResearch.WordTrace]
  refine ⟨246572372965200253781028281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164381581976800169187352187 246572372965200253781028281)
  ·
    refine ⟨184929279723900190335771211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246572372965200253781028281 184929279723900190335771211)
    ·
      refine ⟨277393919585850285503656817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184929279723900190335771211 277393919585850285503656817)
      ·
        refine ⟨208045439689387714127742613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277393919585850285503656817 208045439689387714127742613)
        ·
          refine ⟨9752129985440049099737935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208045439689387714127742613 9752129985440049099737935)
          ·
            refine ⟨14628194978160073649606903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9752129985440049099737935 14628194978160073649606903)
            ·
              refine ⟨21942292467240110474410355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14628194978160073649606903 21942292467240110474410355)
              ·
                refine ⟨32913438700860165711615533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21942292467240110474410355 32913438700860165711615533)
                ·
                  refine ⟨12342539512822562141855825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32913438700860165711615533 12342539512822562141855825)
                  ·
                    refine ⟨9256904634616921606391869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12342539512822562141855825 9256904634616921606391869)
                    ·
                      refine ⟨3471339237981345602396951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9256904634616921606391869 3471339237981345602396951)
                      ·
                        rfl

theorem cell23_6760409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_6760409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760409 prefixEnd_6760409 := by exact prefixLift 6760409
  have htrace : WordTrace (prefixWord ++ tailWord_6760409) baseStart_6760409 baseEnd_6760409 := by
    simpa [prefixWord, tailWord_6760409, baseEnd_6760409] using wordTrace_append hprefix tailTrace_6760409
  have hstable : (prefixWord ++ tailWord_6760409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760409).length < 2 ^ (prefixWord ++ tailWord_6760409).sum := by decide
  have hdescent : baseEnd_6760409 < baseStart_6760409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760426 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_6760426 : Nat := 118140960795 + 6760426 * 2 ^ 59
def prefixEnd_6760426 : Nat := 4983230072969 + 3 ^ 40 * 6760426 * 2
def baseEnd_6760426 : Nat := 3471347967152472035884373

theorem tailTrace_6760426 : CollatzResearch.WordTrace tailWord_6760426 prefixEnd_6760426 3471347967152472035884373 := by
  unfold tailWord_6760426
  simp only [CollatzResearch.WordTrace]
  refine ⟨61643248251534666421099283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164381995337425777122931421 61643248251534666421099283)
  ·
    refine ⟨92464872377301999631648925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61643248251534666421099283 92464872377301999631648925)
    ·
      refine ⟨34674327141488249861868347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92464872377301999631648925 34674327141488249861868347)
      ·
        refine ⟨52011490712232374792802521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34674327141488249861868347 52011490712232374792802521)
        ·
          refine ⟨39008618034174281094601891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52011490712232374792802521 39008618034174281094601891)
          ·
            refine ⟨58512927051261421641902837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39008618034174281094601891 58512927051261421641902837)
            ·
              refine ⟨5485586911055758278928391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58512927051261421641902837 5485586911055758278928391)
              ·
                refine ⟨8228380366583637418392587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5485586911055758278928391 8228380366583637418392587)
                ·
                  refine ⟨12342570549875456127588881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8228380366583637418392587 12342570549875456127588881)
                  ·
                    refine ⟨9256927912406592095691661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12342570549875456127588881 9256927912406592095691661)
                    ·
                      refine ⟨3471347967152472035884373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9256927912406592095691661 3471347967152472035884373)
                      ·
                        rfl

theorem cell23_6760426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_6760426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760426 prefixEnd_6760426 := by exact prefixLift 6760426
  have htrace : WordTrace (prefixWord ++ tailWord_6760426) baseStart_6760426 baseEnd_6760426 := by
    simpa [prefixWord, tailWord_6760426, baseEnd_6760426] using wordTrace_append hprefix tailTrace_6760426
  have hstable : (prefixWord ++ tailWord_6760426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760426).length < 2 ^ (prefixWord ++ tailWord_6760426).sum := by decide
  have hdescent : baseEnd_6760426 < baseStart_6760426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760429 : List Nat := [1, 5, 1, 4, 2, 10]
def baseStart_6760429 : Nat := 118140960795 + 6760429 * 2 ^ 59
def prefixEnd_6760429 : Nat := 4983230072969 + 3 ^ 40 * 6760429 * 2
def baseEnd_6760429 : Nat := 14285388920141709975913

theorem tailTrace_6760429 : CollatzResearch.WordTrace tailWord_6760429 prefixEnd_6760429 14285388920141709975913 := by
  unfold tailWord_6760429
  simp only [CollatzResearch.WordTrace]
  refine ⟨246573102425127797196756341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164382068283418531464504227 246573102425127797196756341)
  ·
    refine ⟨23116228352355730987195907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246573102425127797196756341 23116228352355730987195907)
    ·
      refine ⟨34674342528533596480793861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23116228352355730987195907 34674342528533596480793861)
      ·
        refine ⟨6501439224100049340148849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34674342528533596480793861 6501439224100049340148849)
        ·
          refine ⟨4876079418075037005111637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6501439224100049340148849 4876079418075037005111637)
          ·
            refine ⟨14285388920141709975913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4876079418075037005111637 14285388920141709975913)
            ·
              rfl

theorem cell23_6760429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 10].length) (baseStart_6760429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760429 prefixEnd_6760429 := by exact prefixLift 6760429
  have htrace : WordTrace (prefixWord ++ tailWord_6760429) baseStart_6760429 baseEnd_6760429 := by
    simpa [prefixWord, tailWord_6760429, baseEnd_6760429] using wordTrace_append hprefix tailTrace_6760429
  have hstable : (prefixWord ++ tailWord_6760429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760429).length < 2 ^ (prefixWord ++ tailWord_6760429).sum := by decide
  have hdescent : baseEnd_6760429 < baseStart_6760429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760435 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 5]
def baseStart_6760435 : Nat := 118140960795 + 6760435 * 2 ^ 59
def prefixEnd_6760435 : Nat := 4983230072969 + 3 ^ 40 * 6760435 * 2
def baseEnd_6760435 : Nat := 3471352588478362500671831

theorem tailTrace_6760435 : CollatzResearch.WordTrace tailWord_6760435 prefixEnd_6760435 3471352588478362500671831 := by
  unfold tailWord_6760435
  simp only [CollatzResearch.WordTrace]
  refine ⟨246573321263106060221474759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164382214175404040147649839 246573321263106060221474759)
  ·
    refine ⟨369859981894659090332212139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246573321263106060221474759 369859981894659090332212139)
    ·
      refine ⟨554789972841988635498318209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369859981894659090332212139 554789972841988635498318209)
      ·
        refine ⟨416092479631491476623738657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554789972841988635498318209 416092479631491476623738657)
        ·
          refine ⟨312069359723618607467803993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416092479631491476623738657 312069359723618607467803993)
          ·
            refine ⟨234052019792713955600852995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312069359723618607467803993 234052019792713955600852995)
            ·
              refine ⟨351078029689070933401279493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234052019792713955600852995 351078029689070933401279493)
              ·
                refine ⟨65827130566700800012739905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351078029689070933401279493 65827130566700800012739905)
                ·
                  refine ⟨49370347925025600009554929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65827130566700800012739905 49370347925025600009554929)
                  ·
                    refine ⟨37027760943769200007166197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49370347925025600009554929 37027760943769200007166197)
                    ·
                      refine ⟨3471352588478362500671831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37027760943769200007166197 3471352588478362500671831)
                      ·
                        rfl

theorem cell23_6760435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_6760435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760435 prefixEnd_6760435 := by exact prefixLift 6760435
  have htrace : WordTrace (prefixWord ++ tailWord_6760435) baseStart_6760435 baseEnd_6760435 := by
    simpa [prefixWord, tailWord_6760435, baseEnd_6760435] using wordTrace_append hprefix tailTrace_6760435
  have hstable : (prefixWord ++ tailWord_6760435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760435).length < 2 ^ (prefixWord ++ tailWord_6760435).sum := by decide
  have hdescent : baseEnd_6760435 < baseStart_6760435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760449 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_6760449 : Nat := 118140960795 + 6760449 * 2 ^ 59
def prefixEnd_6760449 : Nat := 4983230072969 + 3 ^ 40 * 6760449 * 2
def baseEnd_6760449 : Nat := 3471359777207525445896767

theorem tailTrace_6760449 : CollatzResearch.WordTrace tailWord_6760449 prefixEnd_6760449 3471359777207525445896767 := by
  unfold tailWord_6760449
  simp only [CollatzResearch.WordTrace]
  refine ⟨246573831885055340612484401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164382554590036893741656267 246573831885055340612484401)
  ·
    refine ⟨184930373913791505459363301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246573831885055340612484401 184930373913791505459363301)
    ·
      refine ⟨34674445108835907273630619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184930373913791505459363301 34674445108835907273630619)
      ·
        refine ⟨52011667663253860910445929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34674445108835907273630619 52011667663253860910445929)
        ·
          refine ⟨39008750747440395682834447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52011667663253860910445929 39008750747440395682834447)
          ·
            refine ⟨58513126121160593524251671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39008750747440395682834447 58513126121160593524251671)
            ·
              refine ⟨87769689181740890286377507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58513126121160593524251671 87769689181740890286377507)
              ·
                refine ⟨131654533772611335429566261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87769689181740890286377507 131654533772611335429566261)
                ·
                  refine ⟨12342612541182312696521837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131654533772611335429566261 12342612541182312696521837)
                  ·
                    refine ⟨4628479702943367261195689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12342612541182312696521837 4628479702943367261195689)
                    ·
                      refine ⟨3471359777207525445896767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628479702943367261195689 3471359777207525445896767)
                      ·
                        rfl

theorem cell23_6760449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_6760449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760449 prefixEnd_6760449 := by exact prefixLift 6760449
  have htrace : WordTrace (prefixWord ++ tailWord_6760449) baseStart_6760449 baseEnd_6760449 := by
    simpa [prefixWord, tailWord_6760449, baseEnd_6760449] using wordTrace_append hprefix tailTrace_6760449
  have hstable : (prefixWord ++ tailWord_6760449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760449).length < 2 ^ (prefixWord ++ tailWord_6760449).sum := by decide
  have hdescent : baseEnd_6760449 < baseStart_6760449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760462 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_6760462 : Nat := 118140960795 + 6760462 * 2 ^ 59
def prefixEnd_6760462 : Nat := 4983230072969 + 3 ^ 40 * 6760462 * 2
def baseEnd_6760462 : Nat := 3471366452456033895034207

theorem tailTrace_6760462 : CollatzResearch.WordTrace tailWord_6760462 prefixEnd_6760462 3471366452456033895034207 := by
  unfold tailWord_6760462
  simp only [CollatzResearch.WordTrace]
  refine ⟨30821788254251030479088455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164382870689338829221805093 30821788254251030479088455)
  ·
    refine ⟨46232682381376545718632683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30821788254251030479088455 46232682381376545718632683)
    ·
      refine ⟨69349023572064818577949025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46232682381376545718632683 69349023572064818577949025)
      ·
        refine ⟨52011767679048613933461769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69349023572064818577949025 52011767679048613933461769)
        ·
          refine ⟨39008825759286460450096327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52011767679048613933461769 39008825759286460450096327)
          ·
            refine ⟨58513238638929690675144491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39008825759286460450096327 58513238638929690675144491)
            ·
              refine ⟨87769857958394536012716737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58513238638929690675144491 87769857958394536012716737)
              ·
                refine ⟨65827393468795902009537553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87769857958394536012716737 65827393468795902009537553)
                ·
                  refine ⟨49370545101596926507153165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65827393468795902009537553 49370545101596926507153165)
                  ·
                    refine ⟨18513954413098847440182437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49370545101596926507153165 18513954413098847440182437)
                    ·
                      refine ⟨3471366452456033895034207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18513954413098847440182437 3471366452456033895034207)
                      ·
                        rfl

theorem cell23_6760462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_6760462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760462 prefixEnd_6760462 := by exact prefixLift 6760462
  have htrace : WordTrace (prefixWord ++ tailWord_6760462) baseStart_6760462 baseEnd_6760462 := by
    simpa [prefixWord, tailWord_6760462, baseEnd_6760462] using wordTrace_append hprefix tailTrace_6760462
  have hstable : (prefixWord ++ tailWord_6760462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760462).length < 2 ^ (prefixWord ++ tailWord_6760462).sum := by decide
  have hdescent : baseEnd_6760462 < baseStart_6760462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760479 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 1, 4, 2]
def baseStart_6760479 : Nat := 118140960795 + 6760479 * 2 ^ 59
def prefixEnd_6760479 : Nat := 4983230072969 + 3 ^ 40 * 6760479 * 2
def baseEnd_6760479 : Nat := 3471375181627160328521629

theorem tailTrace_6760479 : CollatzResearch.WordTrace tailWord_6760479 prefixEnd_6760479 3471375181627160328521629 := by
  unfold tailWord_6760479
  simp only [CollatzResearch.WordTrace]
  refine ⟨246574926074946655736076491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164383284049964437157384327 246574926074946655736076491)
  ·
    refine ⟨369862389112419983604114737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246574926074946655736076491 369862389112419983604114737)
    ·
      refine ⟨277396791834314987703086053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369862389112419983604114737 277396791834314987703086053)
      ·
        refine ⟨52011898468934060194328635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277396791834314987703086053 52011898468934060194328635)
        ·
          refine ⟨78017847703401090291492953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52011898468934060194328635 78017847703401090291492953)
          ·
            refine ⟨58513385777550817718619715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78017847703401090291492953 58513385777550817718619715)
            ·
              refine ⟨87770078666326226577929573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58513385777550817718619715 87770078666326226577929573)
              ·
                refine ⟨16456889749936167483361795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87770078666326226577929573 16456889749936167483361795)
                ·
                  refine ⟨24685334624904251225042693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16456889749936167483361795 24685334624904251225042693)
                  ·
                    refine ⟨4628500242169547104695505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24685334624904251225042693 4628500242169547104695505)
                    ·
                      refine ⟨3471375181627160328521629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628500242169547104695505 3471375181627160328521629)
                      ·
                        rfl

theorem cell23_6760479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_6760479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760479 prefixEnd_6760479 := by exact prefixLift 6760479
  have htrace : WordTrace (prefixWord ++ tailWord_6760479) baseStart_6760479 baseEnd_6760479 := by
    simpa [prefixWord, tailWord_6760479, baseEnd_6760479] using wordTrace_append hprefix tailTrace_6760479
  have hstable : (prefixWord ++ tailWord_6760479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760479).length < 2 ^ (prefixWord ++ tailWord_6760479).sum := by decide
  have hdescent : baseEnd_6760479 < baseStart_6760479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760482 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_6760482 : Nat := 118140960795 + 6760482 * 2 ^ 59
def prefixEnd_6760482 : Nat := 4983230072969 + 3 ^ 40 * 6760482 * 2
def baseEnd_6760482 : Nat := 3471376722069123816784115

theorem tailTrace_6760482 : CollatzResearch.WordTrace tailWord_6760482 prefixEnd_6760482 3471376722069123816784115 := by
  unfold tailWord_6760482
  simp only [CollatzResearch.WordTrace]
  refine ⟨61643758873483946812108925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164383356995957191498957133 61643758873483946812108925)
  ·
    refine ⟨23116409577556480054540847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61643758873483946812108925 23116409577556480054540847)
    ·
      refine ⟨34674614366334720081811271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23116409577556480054540847 34674614366334720081811271)
      ·
        refine ⟨52011921549502080122716907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34674614366334720081811271 52011921549502080122716907)
        ·
          refine ⟨78017882324253120184075361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52011921549502080122716907 78017882324253120184075361)
          ·
            refine ⟨58513411743189840138056521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78017882324253120184075361 58513411743189840138056521)
            ·
              refine ⟨43885058807392380103542391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58513411743189840138056521 43885058807392380103542391)
              ·
                refine ⟨65827588211088570155313587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43885058807392380103542391 65827588211088570155313587)
                ·
                  refine ⟨98741382316632855232970381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65827588211088570155313587 98741382316632855232970381)
                  ·
                    refine ⟨37028018368737320712363893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98741382316632855232970381 37028018368737320712363893)
                    ·
                      refine ⟨3471376722069123816784115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37028018368737320712363893 3471376722069123816784115)
                      ·
                        rfl

theorem cell23_6760482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_6760482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760482 prefixEnd_6760482 := by exact prefixLift 6760482
  have htrace : WordTrace (prefixWord ++ tailWord_6760482) baseStart_6760482 baseEnd_6760482 := by
    simpa [prefixWord, tailWord_6760482, baseEnd_6760482] using wordTrace_append hprefix tailTrace_6760482
  have hstable : (prefixWord ++ tailWord_6760482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760482).length < 2 ^ (prefixWord ++ tailWord_6760482).sum := by decide
  have hdescent : baseEnd_6760482 < baseStart_6760482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760495 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_6760495 : Nat := 118140960795 + 6760495 * 2 ^ 59
def prefixEnd_6760495 : Nat := 4983230072969 + 3 ^ 40 * 6760495 * 2
def baseEnd_6760495 : Nat := 3471383397317632265921555

theorem tailTrace_6760495 : CollatzResearch.WordTrace tailWord_6760495 prefixEnd_6760495 3471383397317632265921555 := by
  unfold tailWord_6760495
  simp only [CollatzResearch.WordTrace]
  refine ⟨246575509642888690468658939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164383673095259126979105959 246575509642888690468658939)
  ·
    refine ⟨369863264464333035702988409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246575509642888690468658939 369863264464333035702988409)
    ·
      refine ⟨277397448348249776777241307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369863264464333035702988409 277397448348249776777241307)
      ·
        refine ⟨416096172522374665165861961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277397448348249776777241307 416096172522374665165861961)
        ·
          refine ⟨312072129391780998874396471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416096172522374665165861961 312072129391780998874396471)
          ·
            refine ⟨468108194087671498311594707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312072129391780998874396471 468108194087671498311594707)
            ·
              refine ⟨702162291131507247467392061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468108194087671498311594707 702162291131507247467392061)
              ·
                refine ⟨263310859174315217800272023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 702162291131507247467392061 263310859174315217800272023)
                ·
                  refine ⟨394966288761472826700408035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263310859174315217800272023 394966288761472826700408035)
                  ·
                    refine ⟨592449433142209240050612053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 394966288761472826700408035 592449433142209240050612053)
                    ·
                      refine ⟨3471383397317632265921555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 592449433142209240050612053 3471383397317632265921555)
                      ·
                        rfl

theorem cell23_6760495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_6760495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760495 prefixEnd_6760495 := by exact prefixLift 6760495
  have htrace : WordTrace (prefixWord ++ tailWord_6760495) baseStart_6760495 baseEnd_6760495 := by
    simpa [prefixWord, tailWord_6760495, baseEnd_6760495] using wordTrace_append hprefix tailTrace_6760495
  have hstable : (prefixWord ++ tailWord_6760495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760495).length < 2 ^ (prefixWord ++ tailWord_6760495).sum := by decide
  have hdescent : baseEnd_6760495 < baseStart_6760495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760496 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 4, 2, 2]
def baseStart_6760496 : Nat := 118140960795 + 6760496 * 2 ^ 59
def prefixEnd_6760496 : Nat := 4983230072969 + 3 ^ 40 * 6760496 * 2
def baseEnd_6760496 : Nat := 3471383910798286762009051

theorem tailTrace_6760496 : CollatzResearch.WordTrace tailWord_6760496 prefixEnd_6760496 3471383910798286762009051 := by
  unfold tailWord_6760496
  simp only [CollatzResearch.WordTrace]
  refine ⟨123287773057942533819722671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164383697410590045092963561 123287773057942533819722671)
  ·
    refine ⟨184931659586913800729584007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123287773057942533819722671 184931659586913800729584007)
    ·
      refine ⟨277397489380370701094376011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184931659586913800729584007 277397489380370701094376011)
      ·
        refine ⟨416096234070556051641564017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277397489380370701094376011 416096234070556051641564017)
        ·
          refine ⟨312072175552917038731173013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416096234070556051641564017 312072175552917038731173013)
          ·
            refine ⟨14628383229042986190523735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 312072175552917038731173013 14628383229042986190523735)
            ·
              refine ⟨21942574843564479285785603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14628383229042986190523735 21942574843564479285785603)
              ·
                refine ⟨32913862265346718928678405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21942574843564479285785603 32913862265346718928678405)
                ·
                  refine ⟨6171349174752509799127201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32913862265346718928678405 6171349174752509799127201)
                  ·
                    refine ⟨4628511881064382349345401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6171349174752509799127201 4628511881064382349345401)
                    ·
                      refine ⟨3471383910798286762009051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628511881064382349345401 3471383910798286762009051)
                      ·
                        rfl

theorem cell23_6760496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 2, 2].length) (baseStart_6760496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760496 prefixEnd_6760496 := by exact prefixLift 6760496
  have htrace : WordTrace (prefixWord ++ tailWord_6760496) baseStart_6760496 baseEnd_6760496 := by
    simpa [prefixWord, tailWord_6760496, baseEnd_6760496] using wordTrace_append hprefix tailTrace_6760496
  have hstable : (prefixWord ++ tailWord_6760496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760496).length < 2 ^ (prefixWord ++ tailWord_6760496).sum := by decide
  have hdescent : baseEnd_6760496 < baseStart_6760496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760513 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_6760513 : Nat := 118140960795 + 6760513 * 2 ^ 59
def prefixEnd_6760513 : Nat := 4983230072969 + 3 ^ 40 * 6760513 * 2
def baseEnd_6760513 : Nat := 3471392639969413195496473

theorem tailTrace_6760513 : CollatzResearch.WordTrace tailWord_6760513 prefixEnd_6760513 3471392639969413195496473 := by
  unfold tailWord_6760513
  simp only [CollatzResearch.WordTrace]
  refine ⟨246576166156823479542814193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164384110771215653028542795 246576166156823479542814193)
  ·
    refine ⟨184932124617617609657110645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246576166156823479542814193 184932124617617609657110645)
    ·
      refine ⟨17337386682901650905354123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184932124617617609657110645 17337386682901650905354123)
      ·
        refine ⟨26006080024352476358031185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17337386682901650905354123 26006080024352476358031185)
        ·
          refine ⟨19504560018264357268523389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26006080024352476358031185 19504560018264357268523389)
          ·
            refine ⟨7314210006849133975696271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19504560018264357268523389 7314210006849133975696271)
            ·
              refine ⟨10971315010273700963544407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7314210006849133975696271 10971315010273700963544407)
              ·
                refine ⟨16456972515410551445316611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10971315010273700963544407 16456972515410551445316611)
                ·
                  refine ⟨24685458773115827167974917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16456972515410551445316611 24685458773115827167974917)
                  ·
                    refine ⟨4628523519959217593995297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24685458773115827167974917 4628523519959217593995297)
                    ·
                      refine ⟨3471392639969413195496473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628523519959217593995297 3471392639969413195496473)
                      ·
                        rfl

theorem cell23_6760513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_6760513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760513 prefixEnd_6760513 := by exact prefixLift 6760513
  have htrace : WordTrace (prefixWord ++ tailWord_6760513) baseStart_6760513 baseEnd_6760513 := by
    simpa [prefixWord, tailWord_6760513, baseEnd_6760513] using wordTrace_append hprefix tailTrace_6760513
  have hstable : (prefixWord ++ tailWord_6760513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760513).length < 2 ^ (prefixWord ++ tailWord_6760513).sum := by decide
  have hdescent : baseEnd_6760513 < baseStart_6760513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760536 : List Nat := [2, 1, 2, 2, 1, 6, 1, 3, 5]
def baseStart_6760536 : Nat := 118140960795 + 6760536 * 2 ^ 59
def prefixEnd_6760536 : Nat := 4983230072969 + 3 ^ 40 * 6760536 * 2
def baseEnd_6760536 : Nat := 385711605558274067278763

theorem tailTrace_6760536 : CollatzResearch.WordTrace tailWord_6760536 prefixEnd_6760536 385711605558274067278763 := by
  unfold tailWord_6760536
  simp only [CollatzResearch.WordTrace]
  refine ⟨123288502517870077235450731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164384670023826769647267641 123288502517870077235450731)
  ·
    refine ⟨184932753776805115853176097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123288502517870077235450731 184932753776805115853176097)
    ·
      refine ⟨138699565332603836889882073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184932753776805115853176097 138699565332603836889882073)
      ·
        refine ⟨104024673999452877667411555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138699565332603836889882073 104024673999452877667411555)
        ·
          refine ⟨156037010999179316501117333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104024673999452877667411555 156037010999179316501117333)
          ·
            refine ⟨7314234890586530460989875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156037010999179316501117333 7314234890586530460989875)
            ·
              refine ⟨10971352335879795691484813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7314234890586530460989875 10971352335879795691484813)
              ·
                refine ⟨4114257125954923384306805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10971352335879795691484813 4114257125954923384306805)
                ·
                  refine ⟨385711605558274067278763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4114257125954923384306805 385711605558274067278763)
                  ·
                    rfl

theorem cell23_6760536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 5].length) (baseStart_6760536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760536 prefixEnd_6760536 := by exact prefixLift 6760536
  have htrace : WordTrace (prefixWord ++ tailWord_6760536) baseStart_6760536 baseEnd_6760536 := by
    simpa [prefixWord, tailWord_6760536, baseEnd_6760536] using wordTrace_append hprefix tailTrace_6760536
  have hstable : (prefixWord ++ tailWord_6760536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760536).length < 2 ^ (prefixWord ++ tailWord_6760536).sum := by decide
  have hdescent : baseEnd_6760536 < baseStart_6760536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760549 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_6760549 : Nat := 118140960795 + 6760549 * 2 ^ 59
def prefixEnd_6760549 : Nat := 4983230072969 + 3 ^ 40 * 6760549 * 2
def baseEnd_6760549 : Nat := 1157137041757658351548769

theorem tailTrace_6760549 : CollatzResearch.WordTrace tailWord_6760549 prefixEnd_6760549 1157137041757658351548769 := by
  unfold tailWord_6760549
  simp only [CollatzResearch.WordTrace]
  refine ⟨246577479184693057691124701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164384986123128705127416467 246577479184693057691124701)
  ·
    refine ⟨92466554694259896634171763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246577479184693057691124701 92466554694259896634171763)
    ·
      refine ⟨138699832041389844951257645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92466554694259896634171763 138699832041389844951257645)
      ·
        refine ⟨52012437015521191856721617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138699832041389844951257645 52012437015521191856721617)
        ·
          refine ⟨39009327761640893892541213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52012437015521191856721617 39009327761640893892541213)
          ·
            refine ⟨14628497910615335209702955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39009327761640893892541213 14628497910615335209702955)
            ·
              refine ⟨21942746865923002814554433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14628497910615335209702955 21942746865923002814554433)
              ·
                refine ⟨16457060149442252110915825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21942746865923002814554433 16457060149442252110915825)
                ·
                  refine ⟨12342795112081689083186869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16457060149442252110915825 12342795112081689083186869)
                  ·
                    refine ⟨1157137041757658351548769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12342795112081689083186869 1157137041757658351548769)
                    ·
                      rfl

theorem cell23_6760549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_6760549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760549 prefixEnd_6760549 := by exact prefixLift 6760549
  have htrace : WordTrace (prefixWord ++ tailWord_6760549) baseStart_6760549 baseEnd_6760549 := by
    simpa [prefixWord, tailWord_6760549, baseEnd_6760549] using wordTrace_append hprefix tailTrace_6760549
  have hstable : (prefixWord ++ tailWord_6760549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760549).length < 2 ^ (prefixWord ++ tailWord_6760549).sum := by decide
  have hdescent : baseEnd_6760549 < baseStart_6760549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760586 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_6760586 : Nat := 118140960795 + 6760586 * 2 ^ 59
def prefixEnd_6760586 : Nat := 4983230072969 + 3 ^ 40 * 6760586 * 2
def baseEnd_6760586 : Nat := 3471430124057191409883637

theorem tailTrace_6760586 : CollatzResearch.WordTrace tailWord_6760586 prefixEnd_6760586 3471430124057191409883637 := by
  unfold tailWord_6760586
  simp only [CollatzResearch.WordTrace]
  refine ⟨61644707171389753252555403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164385885790372675340147741 61644707171389753252555403)
  ·
    refine ⟨92467060757084629878833105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61644707171389753252555403 92467060757084629878833105)
    ·
      refine ⟨69350295567813472409124829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92467060757084629878833105 69350295567813472409124829)
      ·
        refine ⟨26006360837930052153421811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69350295567813472409124829 26006360837930052153421811)
        ·
          refine ⟨39009541256895078230132717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26006360837930052153421811 39009541256895078230132717)
          ·
            refine ⟨14628577971335654336299769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39009541256895078230132717 14628577971335654336299769)
            ·
              refine ⟨10971433478501740752224827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14628577971335654336299769 10971433478501740752224827)
              ·
                refine ⟨16457150217752611128337241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10971433478501740752224827 16457150217752611128337241)
                ·
                  refine ⟨12342862663314458346252931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16457150217752611128337241 12342862663314458346252931)
                  ·
                    refine ⟨18514293994971687519379397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12342862663314458346252931 18514293994971687519379397)
                    ·
                      refine ⟨3471430124057191409883637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18514293994971687519379397 3471430124057191409883637)
                      ·
                        rfl

theorem cell23_6760586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_6760586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760586 prefixEnd_6760586 := by exact prefixLift 6760586
  have htrace : WordTrace (prefixWord ++ tailWord_6760586) baseStart_6760586 baseEnd_6760586 := by
    simpa [prefixWord, tailWord_6760586, baseEnd_6760586] using wordTrace_append hprefix tailTrace_6760586
  have hstable : (prefixWord ++ tailWord_6760586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760586).length < 2 ^ (prefixWord ++ tailWord_6760586).sum := by decide
  have hdescent : baseEnd_6760586 < baseStart_6760586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760609 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 6]
def baseStart_6760609 : Nat := 118140960795 + 6760609 * 2 ^ 59
def prefixEnd_6760609 : Nat := 4983230072969 + 3 ^ 40 * 6760609 * 2
def baseEnd_6760609 : Nat := 385715770456916091099559

theorem tailTrace_6760609 : CollatzResearch.WordTrace tailWord_6760609 prefixEnd_6760609 385715770456916091099559 := by
  unfold tailWord_6760609
  simp only [CollatzResearch.WordTrace]
  refine ⟨246579667564475687938308881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164386445042983791958872587 246579667564475687938308881)
  ·
    refine ⟨184934750673356765953731661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246579667564475687938308881 184934750673356765953731661)
    ·
      refine ⟨69350531502508787232649373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184934750673356765953731661 69350531502508787232649373)
      ·
        refine ⟨26006449313440795212243515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69350531502508787232649373 26006449313440795212243515)
        ·
          refine ⟨39009673970161192818365273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26006449313440795212243515 39009673970161192818365273)
          ·
            refine ⟨29257255477620894613773955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39009673970161192818365273 29257255477620894613773955)
            ·
              refine ⟨43885883216431341920660933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29257255477620894613773955 43885883216431341920660933)
              ·
                refine ⟨8228603103080876610123925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43885883216431341920660933 8228603103080876610123925)
                ·
                  refine ⟨385715770456916091099559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8228603103080876610123925 385715770456916091099559)
                  ·
                    rfl

theorem cell23_6760609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 6].length) (baseStart_6760609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760609 prefixEnd_6760609 := by exact prefixLift 6760609
  have htrace : WordTrace (prefixWord ++ tailWord_6760609) baseStart_6760609 baseEnd_6760609 := by
    simpa [prefixWord, tailWord_6760609, baseEnd_6760609] using wordTrace_append hprefix tailTrace_6760609
  have hstable : (prefixWord ++ tailWord_6760609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760609).length < 2 ^ (prefixWord ++ tailWord_6760609).sum := by decide
  have hdescent : baseEnd_6760609 < baseStart_6760609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760632 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_6760632 : Nat := 118140960795 + 6760632 * 2 ^ 59
def prefixEnd_6760632 : Nat := 4983230072969 + 3 ^ 40 * 6760632 * 2
def baseEnd_6760632 : Nat := 3471453744167298229908425

theorem tailTrace_6760632 : CollatzResearch.WordTrace tailWord_6760632 prefixEnd_6760632 3471453744167298229908425 := by
  unfold tailWord_6760632
  simp only [CollatzResearch.WordTrace]
  refine ⟨123290253221696181433198075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164387004295594908577597433 123290253221696181433198075)
  ·
    refine ⟨184935379832544272149797113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123290253221696181433198075 184935379832544272149797113)
    ·
      refine ⟨138701534874408204112347835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184935379832544272149797113 138701534874408204112347835)
      ·
        refine ⟨208052302311612306168521753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138701534874408204112347835 208052302311612306168521753)
        ·
          refine ⟨156039226733709229626391315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208052302311612306168521753 156039226733709229626391315)
          ·
            refine ⟨234058840100563844439586973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156039226733709229626391315 234058840100563844439586973)
            ·
              refine ⟨87772065037711441664845115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234058840100563844439586973 87772065037711441664845115)
              ·
                refine ⟨131658097556567162497267673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87772065037711441664845115 131658097556567162497267673)
                ·
                  refine ⟨98743573167425371872950755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131658097556567162497267673 98743573167425371872950755)
                  ·
                    refine ⟨148115359751138057809426133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98743573167425371872950755 148115359751138057809426133)
                    ·
                      refine ⟨3471453744167298229908425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148115359751138057809426133 3471453744167298229908425)
                      ·
                        rfl

theorem cell23_6760632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_6760632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760632 prefixEnd_6760632 := by exact prefixLift 6760632
  have htrace : WordTrace (prefixWord ++ tailWord_6760632) baseStart_6760632 baseEnd_6760632 := by
    simpa [prefixWord, tailWord_6760632, baseEnd_6760632] using wordTrace_append hprefix tailTrace_6760632
  have hstable : (prefixWord ++ tailWord_6760632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760632).length < 2 ^ (prefixWord ++ tailWord_6760632).sum := by decide
  have hdescent : baseEnd_6760632 < baseStart_6760632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760639 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 1, 5]
def baseStart_6760639 : Nat := 118140960795 + 6760639 * 2 ^ 59
def prefixEnd_6760639 : Nat := 4983230072969 + 3 ^ 40 * 6760639 * 2
def baseEnd_6760639 : Nat := 1157152446177293234173631

theorem tailTrace_6760639 : CollatzResearch.WordTrace tailWord_6760639 prefixEnd_6760639 1157152446177293234173631 := by
  unfold tailWord_6760639
  simp only [CollatzResearch.WordTrace]
  refine ⟨246580761754367003061900971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164387174502911335374600647 246580761754367003061900971)
  ·
    refine ⟨369871142631550504592851457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246580761754367003061900971 369871142631550504592851457)
    ·
      refine ⟨277403356973662878444638593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369871142631550504592851457 277403356973662878444638593)
      ·
        refine ⟨208052517730247158833478945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277403356973662878444638593 208052517730247158833478945)
        ·
          refine ⟨156039388297685369125109209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208052517730247158833478945 156039388297685369125109209)
          ·
            refine ⟨117029541223264026843831907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156039388297685369125109209 117029541223264026843831907)
            ·
              refine ⟨175544311834896040265747861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117029541223264026843831907 175544311834896040265747861)
              ·
                refine ⟨8228639617260751887456931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175544311834896040265747861 8228639617260751887456931)
                ·
                  refine ⟨12342959425891127831185397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8228639617260751887456931 12342959425891127831185397)
                  ·
                    refine ⟨1157152446177293234173631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12342959425891127831185397 1157152446177293234173631)
                    ·
                      rfl

theorem cell23_6760639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 5].length) (baseStart_6760639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760639 prefixEnd_6760639 := by exact prefixLift 6760639
  have htrace : WordTrace (prefixWord ++ tailWord_6760639) baseStart_6760639 baseEnd_6760639 := by
    simpa [prefixWord, tailWord_6760639, baseEnd_6760639] using wordTrace_append hprefix tailTrace_6760639
  have hstable : (prefixWord ++ tailWord_6760639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760639).length < 2 ^ (prefixWord ++ tailWord_6760639).sum := by decide
  have hdescent : baseEnd_6760639 < baseStart_6760639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760786 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_6760786 : Nat := 118140960795 + 6760786 * 2 ^ 59
def prefixEnd_6760786 : Nat := 4983230072969 + 3 ^ 40 * 6760786 * 2
def baseEnd_6760786 : Nat := 3471532820188090627382717

theorem tailTrace_6760786 : CollatzResearch.WordTrace tailWord_6760786 prefixEnd_6760786 3471532820188090627382717 := by
  unfold tailWord_6760786
  simp only [CollatzResearch.WordTrace]
  refine ⟨61646530821208611791875553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164390748856556298111668141 61646530821208611791875553)
  ·
    refine ⟨46234898115906458843906665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61646530821208611791875553 46234898115906458843906665)
    ·
      refine ⟨34676173586929844132929999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46234898115906458843906665 34676173586929844132929999)
      ·
        refine ⟨52014260380394766199394999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34676173586929844132929999 52014260380394766199394999)
        ·
          refine ⟨78021390570592149299092499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52014260380394766199394999 78021390570592149299092499)
          ·
            refine ⟨117032085855888223948638749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78021390570592149299092499 117032085855888223948638749)
            ·
              refine ⟨43887032195958083980739531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117032085855888223948638749 43887032195958083980739531)
              ·
                refine ⟨65830548293937125971109297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43887032195958083980739531 65830548293937125971109297)
                ·
                  refine ⟨49372911220452844478331973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65830548293937125971109297 49372911220452844478331973)
                  ·
                    refine ⟨9257420853834908339687245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49372911220452844478331973 9257420853834908339687245)
                    ·
                      refine ⟨3471532820188090627382717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9257420853834908339687245 3471532820188090627382717)
                      ·
                        rfl

theorem cell23_6760786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_6760786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760786 prefixEnd_6760786 := by exact prefixLift 6760786
  have htrace : WordTrace (prefixWord ++ tailWord_6760786) baseStart_6760786 baseEnd_6760786 := by
    simpa [prefixWord, tailWord_6760786, baseEnd_6760786] using wordTrace_append hprefix tailTrace_6760786
  have hstable : (prefixWord ++ tailWord_6760786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760786).length < 2 ^ (prefixWord ++ tailWord_6760786).sum := by decide
  have hdescent : baseEnd_6760786 < baseStart_6760786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760800 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 1, 4, 2]
def baseStart_6760800 : Nat := 118140960795 + 6760800 * 2 ^ 59
def prefixEnd_6760800 : Nat := 4983230072969 + 3 ^ 40 * 6760800 * 2
def baseEnd_6760800 : Nat := 3471540008917253572607653

theorem tailTrace_6760800 : CollatzResearch.WordTrace tailWord_6760800 prefixEnd_6760800 3471540008917253572607653 := by
  unfold tailWord_6760800
  simp only [CollatzResearch.WordTrace]
  refine ⟨123293316953391863779255927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164391089271189151705674569 123293316953391863779255927)
  ·
    refine ⟨184939975430087795668883891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123293316953391863779255927 184939975430087795668883891)
    ·
      refine ⟨277409963145131693503325837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184939975430087795668883891 277409963145131693503325837)
      ·
        refine ⟨104028736179424385063747189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277409963145131693503325837 104028736179424385063747189)
        ·
          refine ⟨9752694016821036099726299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104028736179424385063747189 9752694016821036099726299)
          ·
            refine ⟨14629041025231554149589449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9752694016821036099726299 14629041025231554149589449)
            ·
              refine ⟨10971780768923665612192087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14629041025231554149589449 10971780768923665612192087)
              ·
                refine ⟨16457671153385498418288131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10971780768923665612192087 16457671153385498418288131)
                ·
                  refine ⟨24686506730078247627432197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16457671153385498418288131 24686506730078247627432197)
                  ·
                    refine ⟨4628720011889671430143537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24686506730078247627432197 4628720011889671430143537)
                    ·
                      refine ⟨3471540008917253572607653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628720011889671430143537 3471540008917253572607653)
                      ·
                        rfl

theorem cell23_6760800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_6760800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760800 prefixEnd_6760800 := by exact prefixLift 6760800
  have htrace : WordTrace (prefixWord ++ tailWord_6760800) baseStart_6760800 baseEnd_6760800 := by
    simpa [prefixWord, tailWord_6760800, baseEnd_6760800] using wordTrace_append hprefix tailTrace_6760800
  have hstable : (prefixWord ++ tailWord_6760800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760800).length < 2 ^ (prefixWord ++ tailWord_6760800).sum := by decide
  have hdescent : baseEnd_6760800 < baseStart_6760800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760819 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 1, 7]
def baseStart_6760819 : Nat := 118140960795 + 6760819 * 2 ^ 59
def prefixEnd_6760819 : Nat := 4983230072969 + 3 ^ 40 * 6760819 * 2
def baseEnd_6760819 : Nat := 1157183255016562999423355

theorem tailTrace_6760819 : CollatzResearch.WordTrace tailWord_6760819 prefixEnd_6760819 1157183255016562999423355 := by
  unfold tailWord_6760819
  simp only [CollatzResearch.WordTrace]
  refine ⟨246587326893714893803453511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164391551262476595868969007 246587326893714893803453511)
  ·
    refine ⟨369880990340572340705180267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246587326893714893803453511 369880990340572340705180267)
    ·
      refine ⟨554821485510858511057770401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369880990340572340705180267 554821485510858511057770401)
      ·
        refine ⟨416116114133143883293327801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554821485510858511057770401 416116114133143883293327801)
        ·
          refine ⟨312087085599857912469995851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416116114133143883293327801 312087085599857912469995851)
          ·
            refine ⟨468130628399786868704993777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312087085599857912469995851 468130628399786868704993777)
            ·
              refine ⟨351097971299840151528745333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468130628399786868704993777 351097971299840151528745333)
              ·
                refine ⟨32915434809360014205819875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351097971299840151528745333 32915434809360014205819875)
                ·
                  refine ⟨49373152214040021308729813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32915434809360014205819875 49373152214040021308729813)
                  ·
                    refine ⟨1157183255016562999423355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49373152214040021308729813 1157183255016562999423355)
                    ·
                      rfl

theorem cell23_6760819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 7].length) (baseStart_6760819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760819 prefixEnd_6760819 := by exact prefixLift 6760819
  have htrace : WordTrace (prefixWord ++ tailWord_6760819) baseStart_6760819 baseEnd_6760819 := by
    simpa [prefixWord, tailWord_6760819, baseEnd_6760819] using wordTrace_append hprefix tailTrace_6760819
  have hstable : (prefixWord ++ tailWord_6760819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760819).length < 2 ^ (prefixWord ++ tailWord_6760819).sum := by decide
  have hdescent : baseEnd_6760819 < baseStart_6760819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760833 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_6760833 : Nat := 118140960795 + 6760833 * 2 ^ 59
def prefixEnd_6760833 : Nat := 4983230072969 + 3 ^ 40 * 6760833 * 2
def baseEnd_6760833 : Nat := 3471556953778851943495001

theorem tailTrace_6760833 : CollatzResearch.WordTrace tailWord_6760833 prefixEnd_6760833 3471556953778851943495001 := by
  unfold tailWord_6760833
  simp only [CollatzResearch.WordTrace]
  refine ⟨246587837515664174194463153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164391891677109449462975435 246587837515664174194463153)
  ·
    refine ⟨184940878136748130645847365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246587837515664174194463153 184940878136748130645847365)
    ·
      refine ⟨34676414650640274496096381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184940878136748130645847365 34676414650640274496096381)
      ·
        refine ⟨13003655493990102936036143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34676414650640274496096381 13003655493990102936036143)
        ·
          refine ⟨19505483240985154404054215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13003655493990102936036143 19505483240985154404054215)
          ·
            refine ⟨29258224861477731606081323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19505483240985154404054215 29258224861477731606081323)
            ·
              refine ⟨43887337292216597409121985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29258224861477731606081323 43887337292216597409121985)
              ·
                refine ⟨32915502969162448056841489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43887337292216597409121985 32915502969162448056841489)
                ·
                  refine ⟨24686627226871836042631117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32915502969162448056841489 24686627226871836042631117)
                  ·
                    refine ⟨9257485210076938515986669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24686627226871836042631117 9257485210076938515986669)
                    ·
                      refine ⟨3471556953778851943495001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9257485210076938515986669 3471556953778851943495001)
                      ·
                        rfl

theorem cell23_6760833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_6760833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760833 prefixEnd_6760833 := by exact prefixLift 6760833
  have htrace : WordTrace (prefixWord ++ tailWord_6760833) baseStart_6760833 baseEnd_6760833 := by
    simpa [prefixWord, tailWord_6760833, baseEnd_6760833] using wordTrace_append hprefix tailTrace_6760833
  have hstable : (prefixWord ++ tailWord_6760833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760833).length < 2 ^ (prefixWord ++ tailWord_6760833).sum := by decide
  have hdescent : baseEnd_6760833 < baseStart_6760833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760834 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_6760834 : Nat := 118140960795 + 6760834 * 2 ^ 59
def prefixEnd_6760834 : Nat := 4983230072969 + 3 ^ 40 * 6760834 * 2
def baseEnd_6760834 : Nat := 3471557467259506439582497

theorem tailTrace_6760834 : CollatzResearch.WordTrace tailWord_6760834 prefixEnd_6760834 3471557467259506439582497 := by
  unfold tailWord_6760834
  simp only [CollatzResearch.WordTrace]
  refine ⟨61646968497165137841312389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164391915992440367576833037 61646968497165137841312389)
  ·
    refine ⟨11558806593218463345246073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61646968497165137841312389 11558806593218463345246073)
    ·
      refine ⟨8669104944913847508934555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11558806593218463345246073 8669104944913847508934555)
      ·
        refine ⟨13003657417370771263401833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8669104944913847508934555 13003657417370771263401833)
        ·
          refine ⟨9752743063028078447551375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13003657417370771263401833 9752743063028078447551375)
          ·
            refine ⟨14629114594542117671327063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9752743063028078447551375 14629114594542117671327063)
            ·
              refine ⟨21943671891813176506990595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14629114594542117671327063 21943671891813176506990595)
              ·
                refine ⟨32915507837719764760485893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21943671891813176506990595 32915507837719764760485893)
                ·
                  refine ⟨6171657719572455892591105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32915507837719764760485893 6171657719572455892591105)
                  ·
                    refine ⟨4628743289679341919443329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6171657719572455892591105 4628743289679341919443329)
                    ·
                      refine ⟨3471557467259506439582497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628743289679341919443329 3471557467259506439582497)
                      ·
                        rfl

theorem cell23_6760834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_6760834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760834 prefixEnd_6760834 := by exact prefixLift 6760834
  have htrace : WordTrace (prefixWord ++ tailWord_6760834) baseStart_6760834 baseEnd_6760834 := by
    simpa [prefixWord, tailWord_6760834, baseEnd_6760834] using wordTrace_append hprefix tailTrace_6760834
  have hstable : (prefixWord ++ tailWord_6760834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760834).length < 2 ^ (prefixWord ++ tailWord_6760834).sum := by decide
  have hdescent : baseEnd_6760834 < baseStart_6760834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760836 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_6760836 : Nat := 118140960795 + 6760836 * 2 ^ 59
def prefixEnd_6760836 : Nat := 4983230072969 + 3 ^ 40 * 6760836 * 2
def baseEnd_6760836 : Nat := 1157186164740271810585829

theorem tailTrace_6760836 : CollatzResearch.WordTrace tailWord_6760836 prefixEnd_6760836 1157186164740271810585829 := by
  unfold tailWord_6760836
  simp only [CollatzResearch.WordTrace]
  refine ⟨123293973467326652853411181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164391964623102203804548241 123293973467326652853411181)
  ·
    refine ⟨46235240050247494820029193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123293973467326652853411181 46235240050247494820029193)
    ·
      refine ⟨34676430037685621115021895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46235240050247494820029193 34676430037685621115021895)
      ·
        refine ⟨52014645056528431672532843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34676430037685621115021895 52014645056528431672532843)
        ·
          refine ⟨78021967584792647508799265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52014645056528431672532843 78021967584792647508799265)
          ·
            refine ⟨58516475688594485631599449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78021967584792647508799265 58516475688594485631599449)
            ·
              refine ⟨43887356766445864223699587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58516475688594485631599449 43887356766445864223699587)
              ·
                refine ⟨65831035149668796335549381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43887356766445864223699587 65831035149668796335549381)
                ·
                  refine ⟨12343319090562899312915509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65831035149668796335549381 12343319090562899312915509)
                  ·
                    refine ⟨1157186164740271810585829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12343319090562899312915509 1157186164740271810585829)
                    ·
                      rfl

theorem cell23_6760836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_6760836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760836 prefixEnd_6760836 := by exact prefixLift 6760836
  have htrace : WordTrace (prefixWord ++ tailWord_6760836) baseStart_6760836 baseEnd_6760836 := by
    simpa [prefixWord, tailWord_6760836, baseEnd_6760836] using wordTrace_append hprefix tailTrace_6760836
  have hstable : (prefixWord ++ tailWord_6760836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760836).length < 2 ^ (prefixWord ++ tailWord_6760836).sum := by decide
  have hdescent : baseEnd_6760836 < baseStart_6760836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760849 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 4, 8]
def baseStart_6760849 : Nat := 118140960795 + 6760849 * 2 ^ 59
def prefixEnd_6760849 : Nat := 4983230072969 + 3 ^ 40 * 6760849 * 2
def baseEnd_6760849 : Nat := 1157188389823107960298309

theorem tailTrace_6760849 : CollatzResearch.WordTrace tailWord_6760849 prefixEnd_6760849 1157188389823107960298309 := by
  unfold tailWord_6760849
  simp only [CollatzResearch.WordTrace]
  refine ⟨246588421083606208927045601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164392280722404139284697067 246588421083606208927045601)
  ·
    refine ⟨184941315812704656695284201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246588421083606208927045601 184941315812704656695284201)
    ·
      refine ⟨138705986859528492521463151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184941315812704656695284201 138705986859528492521463151)
      ·
        refine ⟨208058980289292738782194727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138705986859528492521463151 208058980289292738782194727)
        ·
          refine ⟨312088470433939108173292091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208058980289292738782194727 312088470433939108173292091)
          ·
            refine ⟨468132705650908662259938137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312088470433939108173292091 468132705650908662259938137)
            ·
              refine ⟨351099529238181496694953603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468132705650908662259938137 351099529238181496694953603)
              ·
                refine ⟨526649293857272245042430405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351099529238181496694953603 526649293857272245042430405)
                ·
                  refine ⟨98746742598238545945455701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526649293857272245042430405 98746742598238545945455701)
                  ·
                    refine ⟨1157188389823107960298309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98746742598238545945455701 1157188389823107960298309)
                    ·
                      rfl

theorem cell23_6760849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_6760849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760849 prefixEnd_6760849 := by exact prefixLift 6760849
  have htrace : WordTrace (prefixWord ++ tailWord_6760849) baseStart_6760849 baseEnd_6760849 := by
    simpa [prefixWord, tailWord_6760849, baseEnd_6760849] using wordTrace_append hprefix tailTrace_6760849
  have hstable : (prefixWord ++ tailWord_6760849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760849).length < 2 ^ (prefixWord ++ tailWord_6760849).sum := by decide
  have hdescent : baseEnd_6760849 < baseStart_6760849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760866 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_6760866 : Nat := 118140960795 + 6760866 * 2 ^ 59
def prefixEnd_6760866 : Nat := 4983230072969 + 3 ^ 40 * 6760866 * 2
def baseEnd_6760866 : Nat := 1157191299546816771460783

theorem tailTrace_6760866 : CollatzResearch.WordTrace tailWord_6760866 prefixEnd_6760866 1157191299546816771460783 := by
  unfold tailWord_6760866
  simp only [CollatzResearch.WordTrace]
  refine ⟨61647260281136155207603613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164392694083029747220276301 61647260281136155207603613)
  ·
    refine ⟨23117722605426058202851355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61647260281136155207603613 23117722605426058202851355)
    ·
      refine ⟨34676583908139087304277033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23117722605426058202851355 34676583908139087304277033)
      ·
        refine ⟨26007437931104315478207775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34676583908139087304277033 26007437931104315478207775)
        ·
          refine ⟨39011156896656473217311663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26007437931104315478207775 39011156896656473217311663)
          ·
            refine ⟨58516735344984709825967495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39011156896656473217311663 58516735344984709825967495)
            ·
              refine ⟨87775103017477064738951243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58516735344984709825967495 87775103017477064738951243)
              ·
                refine ⟨131662654526215597108426865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87775103017477064738951243 131662654526215597108426865)
                ·
                  refine ⟨98746990894661697831320149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131662654526215597108426865 98746990894661697831320149)
                  ·
                    refine ⟨1157191299546816771460783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98746990894661697831320149 1157191299546816771460783)
                    ·
                      rfl

theorem cell23_6760866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_6760866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760866 prefixEnd_6760866 := by exact prefixLift 6760866
  have htrace : WordTrace (prefixWord ++ tailWord_6760866) baseStart_6760866 baseEnd_6760866 := by
    simpa [prefixWord, tailWord_6760866, baseEnd_6760866] using wordTrace_append hprefix tailTrace_6760866
  have hstable : (prefixWord ++ tailWord_6760866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760866).length < 2 ^ (prefixWord ++ tailWord_6760866).sum := by decide
  have hdescent : baseEnd_6760866 < baseStart_6760866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760893 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_6760893 : Nat := 118140960795 + 6760893 * 2 ^ 59
def prefixEnd_6760893 : Nat := 4983230072969 + 3 ^ 40 * 6760893 * 2
def baseEnd_6760893 : Nat := 3471587762618121708744725

theorem tailTrace_6760893 : CollatzResearch.WordTrace tailWord_6760893 prefixEnd_6760893 3471587762618121708744725 := by
  unfold tailWord_6760893
  simp only [CollatzResearch.WordTrace]
  refine ⟨246590025895446804441647333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164393350596964536294431555 246590025895446804441647333)
  ·
    refine ⟨46235629855396275832808875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246590025895446804441647333 46235629855396275832808875)
    ·
      refine ⟨69353444783094413749213313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46235629855396275832808875 69353444783094413749213313)
      ·
        refine ⟨52015083587320810311909985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69353444783094413749213313 52015083587320810311909985)
        ·
          refine ⟨39011312690490607733932489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52015083587320810311909985 39011312690490607733932489)
          ·
            refine ⟨29258484517867955800449367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39011312690490607733932489 29258484517867955800449367)
            ·
              refine ⟨43887726776801933700674051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29258484517867955800449367 43887726776801933700674051)
              ·
                refine ⟨65831590165202900551011077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43887726776801933700674051 65831590165202900551011077)
                ·
                  refine ⟨12343423155975543853314577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65831590165202900551011077 12343423155975543853314577)
                  ·
                    refine ⟨9257567366981657889985933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12343423155975543853314577 9257567366981657889985933)
                    ·
                      refine ⟨3471587762618121708744725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9257567366981657889985933 3471587762618121708744725)
                      ·
                        rfl

theorem cell23_6760893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_6760893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760893 prefixEnd_6760893 := by exact prefixLift 6760893
  have htrace : WordTrace (prefixWord ++ tailWord_6760893) baseStart_6760893 baseEnd_6760893 := by
    simpa [prefixWord, tailWord_6760893, baseEnd_6760893] using wordTrace_append hprefix tailTrace_6760893
  have hstable : (prefixWord ++ tailWord_6760893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760893).length < 2 ^ (prefixWord ++ tailWord_6760893).sum := by decide
  have hdescent : baseEnd_6760893 < baseStart_6760893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760896 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 6]
def baseStart_6760896 : Nat := 118140960795 + 6760896 * 2 ^ 59
def prefixEnd_6760896 : Nat := 4983230072969 + 3 ^ 40 * 6760896 * 2
def baseEnd_6760896 : Nat := 385732144784453910778579

theorem tailTrace_6760896 : CollatzResearch.WordTrace tailWord_6760896 prefixEnd_6760896 385732144784453910778579 := by
  unfold tailWord_6760896
  simp only [CollatzResearch.WordTrace]
  refine ⟨123295067657217967977003271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164393423542957290636004361 123295067657217967977003271)
  ·
    refine ⟨184942601485826951965504907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123295067657217967977003271 184942601485826951965504907)
    ·
      refine ⟨277413902228740427948257361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184942601485826951965504907 277413902228740427948257361)
      ·
        refine ⟨208060426671555320961193021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277413902228740427948257361 208060426671555320961193021)
        ·
          refine ⟨78022660001833245360447383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208060426671555320961193021 78022660001833245360447383)
          ·
            refine ⟨117033990002749868040671075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78022660001833245360447383 117033990002749868040671075)
            ·
              refine ⟨175550985004124802061006613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117033990002749868040671075 175550985004124802061006613)
              ·
                refine ⟨8228952422068350096609685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175550985004124802061006613 8228952422068350096609685)
                ·
                  refine ⟨385732144784453910778579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8228952422068350096609685 385732144784453910778579)
                  ·
                    rfl

theorem cell23_6760896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 6].length) (baseStart_6760896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760896 prefixEnd_6760896 := by exact prefixLift 6760896
  have htrace : WordTrace (prefixWord ++ tailWord_6760896) baseStart_6760896 baseEnd_6760896 := by
    simpa [prefixWord, tailWord_6760896, baseEnd_6760896] using wordTrace_append hprefix tailTrace_6760896
  have hstable : (prefixWord ++ tailWord_6760896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760896).length < 2 ^ (prefixWord ++ tailWord_6760896).sum := by decide
  have hdescent : baseEnd_6760896 < baseStart_6760896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760897 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6760897 : Nat := 118140960795 + 6760897 * 2 ^ 59
def prefixEnd_6760897 : Nat := 4983230072969 + 3 ^ 40 * 6760897 * 2
def baseEnd_6760897 : Nat := 3471589816540739693094707

theorem tailTrace_6760897 : CollatzResearch.WordTrace tailWord_6760897 prefixEnd_6760897 3471589816540739693094707 := by
  unfold tailWord_6760897
  simp only [CollatzResearch.WordTrace]
  refine ⟨246590171787432313124792945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164393447858288208749861963 246590171787432313124792945)
  ·
    refine ⟨184942628840574234843594709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246590171787432313124792945 184942628840574234843594709)
    ·
      refine ⟨4334592863450958629146751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 184942628840574234843594709 4334592863450958629146751)
      ·
        refine ⟨6501889295176437943720127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4334592863450958629146751 6501889295176437943720127)
        ·
          refine ⟨9752833942764656915580191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6501889295176437943720127 9752833942764656915580191)
          ·
            refine ⟨14629250914146985373370287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9752833942764656915580191 14629250914146985373370287)
            ·
              refine ⟨21943876371220478060055431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14629250914146985373370287 21943876371220478060055431)
              ·
                refine ⟨32915814556830717090083147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21943876371220478060055431 32915814556830717090083147)
                ·
                  refine ⟨49373721835246075635124721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32915814556830717090083147 49373721835246075635124721)
                  ·
                    refine ⟨37030291376434556726343541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49373721835246075635124721 37030291376434556726343541)
                    ·
                      refine ⟨3471589816540739693094707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37030291376434556726343541 3471589816540739693094707)
                      ·
                        rfl

theorem cell23_6760897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6760897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760897 prefixEnd_6760897 := by exact prefixLift 6760897
  have htrace : WordTrace (prefixWord ++ tailWord_6760897) baseStart_6760897 baseEnd_6760897 := by
    simpa [prefixWord, tailWord_6760897, baseEnd_6760897] using wordTrace_append hprefix tailTrace_6760897
  have hstable : (prefixWord ++ tailWord_6760897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760897).length < 2 ^ (prefixWord ++ tailWord_6760897).sum := by decide
  have hdescent : baseEnd_6760897 < baseStart_6760897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760956 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_6760956 : Nat := 118140960795 + 6760956 * 2 ^ 59
def prefixEnd_6760956 : Nat := 4983230072969 + 3 ^ 40 * 6760956 * 2
def baseEnd_6760956 : Nat := 1157206703966451654085645

theorem tailTrace_6760956 : CollatzResearch.WordTrace tailWord_6760956 prefixEnd_6760956 1157206703966451654085645 := by
  unfold tailWord_6760956
  simp only [CollatzResearch.WordTrace]
  refine ⟨123296161847109283100595361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164394882462812377467460481 123296161847109283100595361)
  ·
    refine ⟨92472121385331962325446521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123296161847109283100595361 92472121385331962325446521)
    ·
      refine ⟨69354091038998971744084891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92472121385331962325446521 69354091038998971744084891)
      ·
        refine ⟨104031136558498457616127337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69354091038998971744084891 104031136558498457616127337)
        ·
          refine ⟨78023352418873843212095503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104031136558498457616127337 78023352418873843212095503)
          ·
            refine ⟨117035028628310764818143255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78023352418873843212095503 117035028628310764818143255)
            ·
              refine ⟨175552542942466147227214883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117035028628310764818143255 175552542942466147227214883)
              ·
                refine ⟨263328814413699220840822325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175552542942466147227214883 263328814413699220840822325)
                ·
                  refine ⟨24687076351284301953827093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263328814413699220840822325 24687076351284301953827093)
                  ·
                    refine ⟨1157206703966451654085645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24687076351284301953827093 1157206703966451654085645)
                    ·
                      rfl

theorem cell23_6760956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_6760956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760956 prefixEnd_6760956 := by exact prefixLift 6760956
  have htrace : WordTrace (prefixWord ++ tailWord_6760956) baseStart_6760956 baseEnd_6760956 := by
    simpa [prefixWord, tailWord_6760956, baseEnd_6760956] using wordTrace_append hprefix tailTrace_6760956
  have hstable : (prefixWord ++ tailWord_6760956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760956).length < 2 ^ (prefixWord ++ tailWord_6760956).sum := by decide
  have hdescent : baseEnd_6760956 < baseStart_6760956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760957 : List Nat := [1, 4, 1, 1, 1, 3, 3, 4, 1, 1, 3]
def baseStart_6760957 : Nat := 118140960795 + 6760957 * 2 ^ 59
def prefixEnd_6760957 : Nat := 4983230072969 + 3 ^ 40 * 6760957 * 2
def baseEnd_6760957 : Nat := 3471620625380009458344431

theorem tailTrace_6760957 : CollatzResearch.WordTrace tailWord_6760957 prefixEnd_6760957 3471620625380009458344431 := by
  unfold tailWord_6760957
  simp only [CollatzResearch.WordTrace]
  refine ⟨246592360167214943371977125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164394906778143295581318083 246592360167214943371977125)
  ·
    refine ⟨46236067531352801882245711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246592360167214943371977125 46236067531352801882245711)
    ·
      refine ⟨69354101297029202823368567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46236067531352801882245711 69354101297029202823368567)
      ·
        refine ⟨104031151945543804235052851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69354101297029202823368567 104031151945543804235052851)
        ·
          refine ⟨156046727918315706352579277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104031151945543804235052851 156046727918315706352579277)
          ·
            refine ⟨58517522969368389882217229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156046727918315706352579277 58517522969368389882217229)
            ·
              refine ⟨21944071113513146205831461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58517522969368389882217229 21944071113513146205831461)
              ·
                refine ⟨4114513333783714913593399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21944071113513146205831461 4114513333783714913593399)
                ·
                  refine ⟨6171770000675572370390099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114513333783714913593399 6171770000675572370390099)
                  ·
                    refine ⟨9257655001013358555585149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6171770000675572370390099 9257655001013358555585149)
                    ·
                      refine ⟨3471620625380009458344431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9257655001013358555585149 3471620625380009458344431)
                      ·
                        rfl

theorem cell23_6760957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_6760957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760957 prefixEnd_6760957 := by exact prefixLift 6760957
  have htrace : WordTrace (prefixWord ++ tailWord_6760957) baseStart_6760957 baseEnd_6760957 := by
    simpa [prefixWord, tailWord_6760957, baseEnd_6760957] using wordTrace_append hprefix tailTrace_6760957
  have hstable : (prefixWord ++ tailWord_6760957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760957).length < 2 ^ (prefixWord ++ tailWord_6760957).sum := by decide
  have hdescent : baseEnd_6760957 < baseStart_6760957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760986 : List Nat := [3, 1, 1, 3, 1, 1, 2, 11]
def baseStart_6760986 : Nat := 118140960795 + 6760986 * 2 ^ 59
def prefixEnd_6760986 : Nat := 4983230072969 + 3 ^ 40 * 6760986 * 2
def baseEnd_6760986 : Nat := 128579093196999623884511

theorem tailTrace_6760986 : CollatzResearch.WordTrace tailWord_6760986 prefixEnd_6760986 128579093196999623884511 := by
  unfold tailWord_6760986
  simp only [CollatzResearch.WordTrace]
  refine ⟨61648354471027470331195703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164395611922739920883188541 61648354471027470331195703)
  ·
    refine ⟨92472531706541205496793555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61648354471027470331195703 92472531706541205496793555)
    ·
      refine ⟨138708797559811808245190333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92472531706541205496793555 138708797559811808245190333)
      ·
        refine ⟨52015799084929428091946375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138708797559811808245190333 52015799084929428091946375)
        ·
          refine ⟨78023698627394142137919563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52015799084929428091946375 78023698627394142137919563)
          ·
            refine ⟨117035547941091213206879345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78023698627394142137919563 117035547941091213206879345)
            ·
              refine ⟨87776660955818409905159509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117035547941091213206879345 87776660955818409905159509)
              ·
                refine ⟨128579093196999623884511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 87776660955818409905159509 128579093196999623884511)
                ·
                  rfl

theorem cell23_6760986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 11].length) (baseStart_6760986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760986 prefixEnd_6760986 := by exact prefixLift 6760986
  have htrace : WordTrace (prefixWord ++ tailWord_6760986) baseStart_6760986 baseEnd_6760986 := by
    simpa [prefixWord, tailWord_6760986, baseEnd_6760986] using wordTrace_append hprefix tailTrace_6760986
  have hstable : (prefixWord ++ tailWord_6760986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760986).length < 2 ^ (prefixWord ++ tailWord_6760986).sum := by decide
  have hdescent : baseEnd_6760986 < baseStart_6760986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6760993 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6760993 : Nat := 118140960795 + 6760993 * 2 ^ 59
def prefixEnd_6760993 : Nat := 4983230072969 + 3 ^ 40 * 6760993 * 2
def baseEnd_6760993 : Nat := 3471639110683571317494265

theorem tailTrace_6760993 : CollatzResearch.WordTrace tailWord_6760993 prefixEnd_6760993 3471639110683571317494265 := by
  unfold tailWord_6760993
  simp only [CollatzResearch.WordTrace]
  refine ⟨246593673195084521520287633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164395782130056347680191755 246593673195084521520287633)
  ·
    refine ⟨184945254896313391140215725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246593673195084521520287633 184945254896313391140215725)
    ·
      refine ⟨69354470586117521677580897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184945254896313391140215725 69354470586117521677580897)
      ·
        refine ⟨52015852939588141258185673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69354470586117521677580897 52015852939588141258185673)
        ·
          refine ⟨39011889704691105943639255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52015852939588141258185673 39011889704691105943639255)
          ·
            refine ⟨58517834557036658915458883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39011889704691105943639255 58517834557036658915458883)
            ·
              refine ⟨87776751835554988373188325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58517834557036658915458883 87776751835554988373188325)
              ·
                refine ⟨16458140969166560319972811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87776751835554988373188325 16458140969166560319972811)
                ·
                  refine ⟨24687211453749840479959217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16458140969166560319972811 24687211453749840479959217)
                  ·
                    refine ⟨18515408590312380359969413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24687211453749840479959217 18515408590312380359969413)
                    ·
                      refine ⟨3471639110683571317494265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18515408590312380359969413 3471639110683571317494265)
                      ·
                        rfl

theorem cell23_6760993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6760993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6760993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6760993 prefixEnd_6760993 := by exact prefixLift 6760993
  have htrace : WordTrace (prefixWord ++ tailWord_6760993) baseStart_6760993 baseEnd_6760993 := by
    simpa [prefixWord, tailWord_6760993, baseEnd_6760993] using wordTrace_append hprefix tailTrace_6760993
  have hstable : (prefixWord ++ tailWord_6760993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6760993).length < 2 ^ (prefixWord ++ tailWord_6760993).sum := by decide
  have hdescent : baseEnd_6760993 < baseStart_6760993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6760993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761014 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_6761014 : Nat := 118140960795 + 6761014 * 2 ^ 59
def prefixEnd_6761014 : Nat := 4983230072969 + 3 ^ 40 * 6761014 * 2
def baseEnd_6761014 : Nat := 3471649893777315735331669

theorem tailTrace_6761014 : CollatzResearch.WordTrace tailWord_6761014 prefixEnd_6761014 3471649893777315735331669 := by
  unfold tailWord_6761014
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412152445500527631675131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164396292752005628071201397 15412152445500527631675131)
  ·
    refine ⟨23118228668250791447512697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15412152445500527631675131 23118228668250791447512697)
    ·
      refine ⟨17338671501188093585634523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23118228668250791447512697 17338671501188093585634523)
      ·
        refine ⟨26008007251782140378451785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17338671501188093585634523 26008007251782140378451785)
        ·
          refine ⟨19506005438836605283838839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26008007251782140378451785 19506005438836605283838839)
          ·
            refine ⟨29259008158254907925758259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19506005438836605283838839 29259008158254907925758259)
            ·
              refine ⟨43888512237382361888637389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29259008158254907925758259 43888512237382361888637389)
              ·
                refine ⟨16458192089018385708239021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43888512237382361888637389 16458192089018385708239021)
                ·
                  refine ⟨6171822033381894640589633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16458192089018385708239021 6171822033381894640589633)
                  ·
                    refine ⟨4628866525036420980442225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6171822033381894640589633 4628866525036420980442225)
                    ·
                      refine ⟨3471649893777315735331669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628866525036420980442225 3471649893777315735331669)
                      ·
                        rfl

theorem cell23_6761014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_6761014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761014 prefixEnd_6761014 := by exact prefixLift 6761014
  have htrace : WordTrace (prefixWord ++ tailWord_6761014) baseStart_6761014 baseEnd_6761014 := by
    simpa [prefixWord, tailWord_6761014, baseEnd_6761014] using wordTrace_append hprefix tailTrace_6761014
  have hstable : (prefixWord ++ tailWord_6761014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761014).length < 2 ^ (prefixWord ++ tailWord_6761014).sum := by decide
  have hdescent : baseEnd_6761014 < baseStart_6761014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761037 : List Nat := [1, 6, 1, 1, 2, 3, 2, 7]
def baseStart_6761037 : Nat := 118140960795 + 6761037 * 2 ^ 59
def prefixEnd_6761037 : Nat := 4983230072969 + 3 ^ 40 * 6761037 * 2
def baseEnd_6761037 : Nat := 128580063104902560938669

theorem tailTrace_6761037 : CollatzResearch.WordTrace tailWord_6761037 prefixEnd_6761037 128580063104902560938669 := by
  unfold tailWord_6761037
  simp only [CollatzResearch.WordTrace]
  refine ⟨246595278006925117034889365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164396852004616744689926243 246595278006925117034889365)
  ·
    refine ⟨11559153656574614861010439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 246595278006925117034889365 11559153656574614861010439)
    ·
      refine ⟨17338730484861922291515659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11559153656574614861010439 17338730484861922291515659)
      ·
        refine ⟨26008095727292883437273489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17338730484861922291515659 26008095727292883437273489)
        ·
          refine ⟨19506071795469662577955117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26008095727292883437273489 19506071795469662577955117)
          ·
            refine ⟨7314776923301123466733169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19506071795469662577955117 7314776923301123466733169)
            ·
              refine ⟨5486082692475842600049877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7314776923301123466733169 5486082692475842600049877)
              ·
                refine ⟨128580063104902560938669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5486082692475842600049877 128580063104902560938669)
                ·
                  rfl

theorem cell23_6761037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 7].length) (baseStart_6761037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761037 prefixEnd_6761037 := by exact prefixLift 6761037
  have htrace : WordTrace (prefixWord ++ tailWord_6761037) baseStart_6761037 baseEnd_6761037 := by
    simpa [prefixWord, tailWord_6761037, baseEnd_6761037] using wordTrace_append hprefix tailTrace_6761037
  have hstable : (prefixWord ++ tailWord_6761037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761037).length < 2 ^ (prefixWord ++ tailWord_6761037).sum := by decide
  have hdescent : baseEnd_6761037 < baseStart_6761037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761054 : List Nat := [4, 4, 1, 2, 1, 2, 9]
def baseStart_6761054 : Nat := 118140960795 + 6761054 * 2 ^ 59
def prefixEnd_6761054 : Nat := 4983230072969 + 3 ^ 40 * 6761054 * 2
def baseEnd_6761054 : Nat := 42860128802512291096685

theorem tailTrace_6761054 : CollatzResearch.WordTrace tailWord_6761054 prefixEnd_6761054 42860128802512291096685 := by
  unfold tailWord_6761054
  simp only [CollatzResearch.WordTrace]
  refine ⟨30824487255982941117282277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164397265365242352625505477 30824487255982941117282277)
  ·
    refine ⟨5779591360496801459490427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30824487255982941117282277 5779591360496801459490427)
    ·
      refine ⟨8669387040745202189235641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5779591360496801459490427 8669387040745202189235641)
      ·
        refine ⟨6502040280558901641926731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8669387040745202189235641 6502040280558901641926731)
        ·
          refine ⟨9753060420838352462890097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502040280558901641926731 9753060420838352462890097)
          ·
            refine ⟨7314795315628764347167573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9753060420838352462890097 7314795315628764347167573)
            ·
              refine ⟨42860128802512291096685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7314795315628764347167573 42860128802512291096685)
              ·
                rfl

theorem cell23_6761054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 9].length) (baseStart_6761054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761054 prefixEnd_6761054 := by exact prefixLift 6761054
  have htrace : WordTrace (prefixWord ++ tailWord_6761054) baseStart_6761054 baseEnd_6761054 := by
    simpa [prefixWord, tailWord_6761054, baseEnd_6761054] using wordTrace_append hprefix tailTrace_6761054
  have hstable : (prefixWord ++ tailWord_6761054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761054).length < 2 ^ (prefixWord ++ tailWord_6761054).sum := by decide
  have hdescent : baseEnd_6761054 < baseStart_6761054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761057 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_6761057 : Nat := 118140960795 + 6761057 * 2 ^ 59
def prefixEnd_6761057 : Nat := 4983230072969 + 3 ^ 40 * 6761057 * 2
def baseEnd_6761057 : Nat := 3471671973445459067093971

theorem tailTrace_6761057 : CollatzResearch.WordTrace tailWord_6761057 prefixEnd_6761057 3471671973445459067093971 := by
  unfold tailWord_6761057
  simp only [CollatzResearch.WordTrace]
  refine ⟨246596007466852660450617425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164397338311235106967078283 246596007466852660450617425)
  ·
    refine ⟨184947005600139495337963069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246596007466852660450617425 184947005600139495337963069)
    ·
      refine ⟨69355127100052310751736151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184947005600139495337963069 69355127100052310751736151)
      ·
        refine ⟨104032690650078466127604227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69355127100052310751736151 104032690650078466127604227)
        ·
          refine ⟨156049035975117699191406341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104032690650078466127604227 156049035975117699191406341)
          ·
            refine ⟨29259194245334568598388689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156049035975117699191406341 29259194245334568598388689)
            ·
              refine ⟨21944395684000926448791517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29259194245334568598388689 21944395684000926448791517)
              ·
                refine ⟨8229148381500347418296819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21944395684000926448791517 8229148381500347418296819)
                ·
                  refine ⟨12343722572250521127445229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229148381500347418296819 12343722572250521127445229)
                  ·
                    refine ⟨4628895964593945422791961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12343722572250521127445229 4628895964593945422791961)
                    ·
                      refine ⟨3471671973445459067093971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628895964593945422791961 3471671973445459067093971)
                      ·
                        rfl

theorem cell23_6761057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_6761057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761057 prefixEnd_6761057 := by exact prefixLift 6761057
  have htrace : WordTrace (prefixWord ++ tailWord_6761057) baseStart_6761057 baseEnd_6761057 := by
    simpa [prefixWord, tailWord_6761057, baseEnd_6761057] using wordTrace_append hprefix tailTrace_6761057
  have hstable : (prefixWord ++ tailWord_6761057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761057).length < 2 ^ (prefixWord ++ tailWord_6761057).sum := by decide
  have hdescent : baseEnd_6761057 < baseStart_6761057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761103 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 3]
def baseStart_6761103 : Nat := 118140960795 + 6761103 * 2 ^ 59
def prefixEnd_6761103 : Nat := 4983230072969 + 3 ^ 40 * 6761103 * 2
def baseEnd_6761103 : Nat := 3471695593555565887118759

theorem tailTrace_6761103 : CollatzResearch.WordTrace tailWord_6761103 prefixEnd_6761103 3471695593555565887118759 := by
  unfold tailWord_6761103
  simp only [CollatzResearch.WordTrace]
  refine ⟨246597685224686010306791963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164398456816457340204527975 246597685224686010306791963)
  ·
    refine ⟨369896527837029015460187945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246597685224686010306791963 369896527837029015460187945)
    ·
      refine ⟨277422395877771761595140959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369896527837029015460187945 277422395877771761595140959)
      ·
        refine ⟨416133593816657642392711439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277422395877771761595140959 416133593816657642392711439)
        ·
          refine ⟨624200390724986463589067159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416133593816657642392711439 624200390724986463589067159)
          ·
            refine ⟨936300586087479695383600739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624200390724986463589067159 936300586087479695383600739)
            ·
              refine ⟨1404450879131219543075401109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936300586087479695383600739 1404450879131219543075401109)
              ·
                refine ⟨65833634959275916081659427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1404450879131219543075401109 65833634959275916081659427)
                ·
                  refine ⟨98750452438913874122489141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65833634959275916081659427 98750452438913874122489141)
                  ·
                    refine ⟨9257854916148175698983357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98750452438913874122489141 9257854916148175698983357)
                    ·
                      refine ⟨3471695593555565887118759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9257854916148175698983357 3471695593555565887118759)
                      ·
                        rfl

theorem cell23_6761103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_6761103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761103 prefixEnd_6761103 := by exact prefixLift 6761103
  have htrace : WordTrace (prefixWord ++ tailWord_6761103) baseStart_6761103 baseEnd_6761103 := by
    simpa [prefixWord, tailWord_6761103, baseEnd_6761103] using wordTrace_append hprefix tailTrace_6761103
  have hstable : (prefixWord ++ tailWord_6761103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761103).length < 2 ^ (prefixWord ++ tailWord_6761103).sum := by decide
  have hdescent : baseEnd_6761103 < baseStart_6761103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761121 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_6761121 : Nat := 118140960795 + 6761121 * 2 ^ 59
def prefixEnd_6761121 : Nat := 4983230072969 + 3 ^ 40 * 6761121 * 2
def baseEnd_6761121 : Nat := 3471704836207346816693677

theorem tailTrace_6761121 : CollatzResearch.WordTrace tailWord_6761121 prefixEnd_6761121 3471704836207346816693677 := by
  unfold tailWord_6761121
  simp only [CollatzResearch.WordTrace]
  refine ⟨246598341738620799380947217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164398894492413866253964811 246598341738620799380947217)
  ·
    refine ⟨184948756303965599535710413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246598341738620799380947217 184948756303965599535710413)
    ·
      refine ⟨69355783613987099825891405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184948756303965599535710413 69355783613987099825891405)
      ·
        refine ⟨26008418855245162434709277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69355783613987099825891405 26008418855245162434709277)
        ·
          refine ⟨9753157070716935913015979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26008418855245162434709277 9753157070716935913015979)
          ·
            refine ⟨14629735606075403869523969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9753157070716935913015979 14629735606075403869523969)
            ·
              refine ⟨10972301704556552902142977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14629735606075403869523969 10972301704556552902142977)
              ·
                refine ⟨8229226278417414676607233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10972301704556552902142977 8229226278417414676607233)
                ·
                  refine ⟨6171919708813061007455425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8229226278417414676607233 6171919708813061007455425)
                  ·
                    refine ⟨4628939781609795755591569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6171919708813061007455425 4628939781609795755591569)
                    ·
                      refine ⟨3471704836207346816693677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4628939781609795755591569 3471704836207346816693677)
                      ·
                        rfl

theorem cell23_6761121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_6761121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761121 prefixEnd_6761121 := by exact prefixLift 6761121
  have htrace : WordTrace (prefixWord ++ tailWord_6761121) baseStart_6761121 baseEnd_6761121 := by
    simpa [prefixWord, tailWord_6761121, baseEnd_6761121] using wordTrace_append hprefix tailTrace_6761121
  have hstable : (prefixWord ++ tailWord_6761121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761121).length < 2 ^ (prefixWord ++ tailWord_6761121).sum := by decide
  have hdescent : baseEnd_6761121 < baseStart_6761121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761123 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 4, 5]
def baseStart_6761123 : Nat := 118140960795 + 6761123 * 2 ^ 59
def prefixEnd_6761123 : Nat := 4983230072969 + 3 ^ 40 * 6761123 * 2
def baseEnd_6761123 : Nat := 1157235287722885269622889

theorem tailTrace_6761123 : CollatzResearch.WordTrace tailWord_6761123 prefixEnd_6761123 1157235287722885269622889 := by
  unfold tailWord_6761123
  simp only [CollatzResearch.WordTrace]
  refine ⟨246598414684613553722520023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164398943123075702481680015 246598414684613553722520023)
  ·
    refine ⟨369897622026920330583780035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246598414684613553722520023 369897622026920330583780035)
    ·
      refine ⟨554846433040380495875670053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369897622026920330583780035 554846433040380495875670053)
      ·
        refine ⟨104033706195071342976688135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 554846433040380495875670053 104033706195071342976688135)
        ·
          refine ⟨156050559292607014465032203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104033706195071342976688135 156050559292607014465032203)
          ·
            refine ⟨234075838938910521697548305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156050559292607014465032203 234075838938910521697548305)
            ·
              refine ⟨175556879204182891273161229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234075838938910521697548305 175556879204182891273161229)
              ·
                refine ⟨65833829701568584227435461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175556879204182891273161229 65833829701568584227435461)
                ·
                  refine ⟨12343843069044109542644149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65833829701568584227435461 12343843069044109542644149)
                  ·
                    refine ⟨1157235287722885269622889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12343843069044109542644149 1157235287722885269622889)
                    ·
                      rfl

theorem cell23_6761123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 5].length) (baseStart_6761123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761123 prefixEnd_6761123 := by exact prefixLift 6761123
  have htrace : WordTrace (prefixWord ++ tailWord_6761123) baseStart_6761123 baseEnd_6761123 := by
    simpa [prefixWord, tailWord_6761123, baseEnd_6761123] using wordTrace_append hprefix tailTrace_6761123
  have hstable : (prefixWord ++ tailWord_6761123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761123).length < 2 ^ (prefixWord ++ tailWord_6761123).sum := by decide
  have hdescent : baseEnd_6761123 < baseStart_6761123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761160 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_6761160 : Nat := 118140960795 + 6761160 * 2 ^ 59
def prefixEnd_6761160 : Nat := 4983230072969 + 3 ^ 40 * 6761160 * 2
def baseEnd_6761160 : Nat := 3471724861952872164105997

theorem tailTrace_6761160 : CollatzResearch.WordTrace tailWord_6761160 prefixEnd_6761160 3471724861952872164105997 := by
  unfold tailWord_6761160
  simp only [CollatzResearch.WordTrace]
  refine ⟨123299882092739754520808467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164399842790319672694411289 123299882092739754520808467)
  ·
    refine ⟨184949823139109631781212701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123299882092739754520808467 184949823139109631781212701)
    ·
      refine ⟨69356183677166111917954763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184949823139109631781212701 69356183677166111917954763)
      ·
        refine ⟨104034275515749167876932145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69356183677166111917954763 104034275515749167876932145)
        ·
          refine ⟨78025706636811875907699109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104034275515749167876932145 78025706636811875907699109)
          ·
            refine ⟨14629819994402226732693583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78025706636811875907699109 14629819994402226732693583)
            ·
              refine ⟨21944729991603340099040375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14629819994402226732693583 21944729991603340099040375)
              ·
                refine ⟨32917094987405010148560563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21944729991603340099040375 32917094987405010148560563)
                ·
                  refine ⟨49375642481107515222840845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32917094987405010148560563 49375642481107515222840845)
                  ·
                    refine ⟨18515865930415318208565317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49375642481107515222840845 18515865930415318208565317)
                    ·
                      refine ⟨3471724861952872164105997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18515865930415318208565317 3471724861952872164105997)
                      ·
                        rfl

theorem cell23_6761160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_6761160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761160 prefixEnd_6761160 := by exact prefixLift 6761160
  have htrace : WordTrace (prefixWord ++ tailWord_6761160) baseStart_6761160 baseEnd_6761160 := by
    simpa [prefixWord, tailWord_6761160, baseEnd_6761160] using wordTrace_append hprefix tailTrace_6761160
  have hstable : (prefixWord ++ tailWord_6761160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761160).length < 2 ^ (prefixWord ++ tailWord_6761160).sum := by decide
  have hdescent : baseEnd_6761160 < baseStart_6761160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761187 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 3, 4]
def baseStart_6761187 : Nat := 118140960795 + 6761187 * 2 ^ 59
def prefixEnd_6761187 : Nat := 4983230072969 + 3 ^ 40 * 6761187 * 2
def baseEnd_6761187 : Nat := 1157246241976847852822791

theorem tailTrace_6761187 : CollatzResearch.WordTrace tailWord_6761187 prefixEnd_6761187 1157246241976847852822791 := by
  unfold tailWord_6761187
  simp only [CollatzResearch.WordTrace]
  refine ⟨246600748956381692652849815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164400499304254461768566543 246600748956381692652849815)
  ·
    refine ⟨369901123434572538979274723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246600748956381692652849815 369901123434572538979274723)
    ·
      refine ⟨554851685151858808468912085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369901123434572538979274723 554851685151858808468912085)
      ·
        refine ⟨13004336370746690823490127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 554851685151858808468912085 13004336370746690823490127)
        ·
          refine ⟨19506504556120036235235191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13004336370746690823490127 19506504556120036235235191)
          ·
            refine ⟨29259756834180054352852787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19506504556120036235235191 29259756834180054352852787)
            ·
              refine ⟨43889635251270081529279181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29259756834180054352852787 43889635251270081529279181)
              ·
                refine ⟨16458613219226280573479693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43889635251270081529279181 16458613219226280573479693)
                ·
                  refine ⟨6171979957209855215054885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16458613219226280573479693 6171979957209855215054885)
                  ·
                    refine ⟨1157246241976847852822791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6171979957209855215054885 1157246241976847852822791)
                    ·
                      rfl

theorem cell23_6761187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 4].length) (baseStart_6761187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761187 prefixEnd_6761187 := by exact prefixLift 6761187
  have htrace : WordTrace (prefixWord ++ tailWord_6761187) baseStart_6761187 baseEnd_6761187 := by
    simpa [prefixWord, tailWord_6761187, baseEnd_6761187] using wordTrace_append hprefix tailTrace_6761187
  have hstable : (prefixWord ++ tailWord_6761187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761187).length < 2 ^ (prefixWord ++ tailWord_6761187).sum := by decide
  have hdescent : baseEnd_6761187 < baseStart_6761187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761203 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 6]
def baseStart_6761203 : Nat := 118140960795 + 6761203 * 2 ^ 59
def prefixEnd_6761203 : Nat := 4983230072969 + 3 ^ 40 * 6761203 * 2
def baseEnd_6761203 : Nat := 3471746941621015495868299

theorem tailTrace_6761203 : CollatzResearch.WordTrace tailWord_6761203 prefixEnd_6761203 3471746941621015495868299 := by
  unfold tailWord_6761203
  simp only [CollatzResearch.WordTrace]
  refine ⟨246601332524323727385432263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164400888349549151590288175 246601332524323727385432263)
  ·
    refine ⟨369901998786485591078148395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246601332524323727385432263 369901998786485591078148395)
    ·
      refine ⟨554852998179728386617222593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369901998786485591078148395 554852998179728386617222593)
      ·
        refine ⟨416139748634796289962916945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554852998179728386617222593 416139748634796289962916945)
        ·
          refine ⟨312104811476097217472187709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416139748634796289962916945 312104811476097217472187709)
          ·
            refine ⟨117039304303536456552070391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312104811476097217472187709 117039304303536456552070391)
            ·
              refine ⟨175558956455304684828105587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117039304303536456552070391 175558956455304684828105587)
              ·
                refine ⟨263338434682957027242158381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175558956455304684828105587 263338434682957027242158381)
                ·
                  refine ⟨98751913006108885215809393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263338434682957027242158381 98751913006108885215809393)
                  ·
                    refine ⟨74063934754581663911857045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98751913006108885215809393 74063934754581663911857045)
                    ·
                      refine ⟨3471746941621015495868299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74063934754581663911857045 3471746941621015495868299)
                      ·
                        rfl

theorem cell23_6761203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_6761203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761203 prefixEnd_6761203 := by exact prefixLift 6761203
  have htrace : WordTrace (prefixWord ++ tailWord_6761203) baseStart_6761203 baseEnd_6761203 := by
    simpa [prefixWord, tailWord_6761203, baseEnd_6761203] using wordTrace_append hprefix tailTrace_6761203
  have hstable : (prefixWord ++ tailWord_6761203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761203).length < 2 ^ (prefixWord ++ tailWord_6761203).sum := by decide
  have hdescent : baseEnd_6761203 < baseStart_6761203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761230 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_6761230 : Nat := 118140960795 + 6761230 * 2 ^ 59
def prefixEnd_6761230 : Nat := 4983230072969 + 3 ^ 40 * 6761230 * 2
def baseEnd_6761230 : Nat := 1157253601866228963410225

theorem tailTrace_6761230 : CollatzResearch.WordTrace tailWord_6761230 prefixEnd_6761230 1157253601866228963410225 := by
  unfold tailWord_6761230
  simp only [CollatzResearch.WordTrace]
  refine ⟨30825289661903238874583143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164401544863483940664443429 30825289661903238874583143)
  ·
    refine ⟨46237934492854858311874715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30825289661903238874583143 46237934492854858311874715)
    ·
      refine ⟨69356901739282287467812073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46237934492854858311874715 69356901739282287467812073)
      ·
        refine ⟨52017676304461715600859055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69356901739282287467812073 52017676304461715600859055)
        ·
          refine ⟨78026514456692573401288583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52017676304461715600859055 78026514456692573401288583)
          ·
            refine ⟨117039771685038860101932875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78026514456692573401288583 117039771685038860101932875)
            ·
              refine ⟨175559657527558290152899313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117039771685038860101932875 175559657527558290152899313)
              ·
                refine ⟨131669743145668717614674485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175559657527558290152899313 131669743145668717614674485)
                ·
                  refine ⟨12344038419906442276375733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131669743145668717614674485 12344038419906442276375733)
                  ·
                    refine ⟨1157253601866228963410225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12344038419906442276375733 1157253601866228963410225)
                    ·
                      rfl

theorem cell23_6761230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_6761230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761230 prefixEnd_6761230 := by exact prefixLift 6761230
  have htrace : WordTrace (prefixWord ++ tailWord_6761230) baseStart_6761230 baseEnd_6761230 := by
    simpa [prefixWord, tailWord_6761230, baseEnd_6761230] using wordTrace_append hprefix tailTrace_6761230
  have hstable : (prefixWord ++ tailWord_6761230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761230).length < 2 ^ (prefixWord ++ tailWord_6761230).sum := by decide
  have hdescent : baseEnd_6761230 < baseStart_6761230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761243 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 2, 10]
def baseStart_6761243 : Nat := 118140960795 + 6761243 * 2 ^ 59
def prefixEnd_6761243 : Nat := 4983230072969 + 3 ^ 40 * 6761243 * 2
def baseEnd_6761243 : Nat := 1157255826949065113122705

theorem tailTrace_6761243 : CollatzResearch.WordTrace tailWord_6761243 prefixEnd_6761243 1157255826949065113122705 := by
  unfold tailWord_6761243
  simp only [CollatzResearch.WordTrace]
  refine ⟨246602791444178814216888383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164401860962785876144592255 246602791444178814216888383)
  ·
    refine ⟨369904187166268221325332575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246602791444178814216888383 369904187166268221325332575)
    ·
      refine ⟨554856280749402331987998863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369904187166268221325332575 554856280749402331987998863)
      ·
        refine ⟨832284421124103497981998295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554856280749402331987998863 832284421124103497981998295)
        ·
          refine ⟨1248426631686155246972997443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832284421124103497981998295 1248426631686155246972997443)
          ·
            refine ⟨1872639947529232870459496165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248426631686155246972997443 1872639947529232870459496165)
            ·
              refine ⟨351119990161731163211155531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1872639947529232870459496165 351119990161731163211155531)
              ·
                refine ⟨526679985242596744816733297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351119990161731163211155531 526679985242596744816733297)
                ·
                  refine ⟨395009988931947558612549973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526679985242596744816733297 395009988931947558612549973)
                  ·
                    refine ⟨1157255826949065113122705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 395009988931947558612549973 1157255826949065113122705)
                    ·
                      rfl

theorem cell23_6761243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 10].length) (baseStart_6761243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761243 prefixEnd_6761243 := by exact prefixLift 6761243
  have htrace : WordTrace (prefixWord ++ tailWord_6761243) baseStart_6761243 baseEnd_6761243 := by
    simpa [prefixWord, tailWord_6761243, baseEnd_6761243] using wordTrace_append hprefix tailTrace_6761243
  have hstable : (prefixWord ++ tailWord_6761243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761243).length < 2 ^ (prefixWord ++ tailWord_6761243).sum := by decide
  have hdescent : baseEnd_6761243 < baseStart_6761243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761244 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_6761244 : Nat := 118140960795 + 6761244 * 2 ^ 59
def prefixEnd_6761244 : Nat := 4983230072969 + 3 ^ 40 * 6761244 * 2
def baseEnd_6761244 : Nat := 3471767994327849835455611

theorem tailTrace_6761244 : CollatzResearch.WordTrace tailWord_6761244 prefixEnd_6761244 3471767994327849835455611 := by
  unfold tailWord_6761244
  simp only [CollatzResearch.WordTrace]
  refine ⟨123301413958587595693837393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164401885278116794258449857 123301413958587595693837393)
  ·
    refine ⟨92476060468940696770378045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123301413958587595693837393 92476060468940696770378045)
    ·
      refine ⟨34678522675852761288891767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92476060468940696770378045 34678522675852761288891767)
      ·
        refine ⟨52017784013779141933337651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34678522675852761288891767 52017784013779141933337651)
        ·
          refine ⟨78026676020668712900006477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52017784013779141933337651 78026676020668712900006477)
          ·
            refine ⟨29260003507750767337502429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78026676020668712900006477 29260003507750767337502429)
            ·
              refine ⟨10972501315406537751563411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29260003507750767337502429 10972501315406537751563411)
              ·
                refine ⟨16458751973109806627345117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10972501315406537751563411 16458751973109806627345117)
                ·
                  refine ⟨6172031989916177485254419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16458751973109806627345117 6172031989916177485254419)
                  ·
                    refine ⟨9258047984874266227881629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6172031989916177485254419 9258047984874266227881629)
                    ·
                      refine ⟨3471767994327849835455611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258047984874266227881629 3471767994327849835455611)
                      ·
                        rfl

theorem cell23_6761244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_6761244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761244 prefixEnd_6761244 := by exact prefixLift 6761244
  have htrace : WordTrace (prefixWord ++ tailWord_6761244) baseStart_6761244 baseEnd_6761244 := by
    simpa [prefixWord, tailWord_6761244, baseEnd_6761244] using wordTrace_append hprefix tailTrace_6761244
  have hstable : (prefixWord ++ tailWord_6761244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761244).length < 2 ^ (prefixWord ++ tailWord_6761244).sum := by decide
  have hdescent : baseEnd_6761244 < baseStart_6761244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761260 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_6761260 : Nat := 118140960795 + 6761260 * 2 ^ 59
def prefixEnd_6761260 : Nat := 4983230072969 + 3 ^ 40 * 6761260 * 2
def baseEnd_6761260 : Nat := 1157258736672773924285179

theorem tailTrace_6761260 : CollatzResearch.WordTrace tailWord_6761260 prefixEnd_6761260 1157258736672773924285179 := by
  unfold tailWord_6761260
  simp only [CollatzResearch.WordTrace]
  refine ⟨123301705742558613060128617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164402274323411484080171489 123301705742558613060128617)
  ·
    refine ⟨92476279306918959795096463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123301705742558613060128617 92476279306918959795096463)
    ·
      refine ⟨138714418960378439692644695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92476279306918959795096463 138714418960378439692644695)
      ·
        refine ⟨208071628440567659538967043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138714418960378439692644695 208071628440567659538967043)
        ·
          refine ⟨312107442660851489308450565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208071628440567659538967043 312107442660851489308450565)
          ·
            refine ⟨58520145498909654245334481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312107442660851489308450565 58520145498909654245334481)
            ·
              refine ⟨43890109124182240684000861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58520145498909654245334481 43890109124182240684000861)
              ·
                refine ⟨16458790921568340256500323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43890109124182240684000861 16458790921568340256500323)
                ·
                  refine ⟨24688186382352510384750485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16458790921568340256500323 24688186382352510384750485)
                  ·
                    refine ⟨1157258736672773924285179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24688186382352510384750485 1157258736672773924285179)
                    ·
                      rfl

theorem cell23_6761260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_6761260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761260 prefixEnd_6761260 := by exact prefixLift 6761260
  have htrace : WordTrace (prefixWord ++ tailWord_6761260) baseStart_6761260 baseEnd_6761260 := by
    simpa [prefixWord, tailWord_6761260, baseEnd_6761260] using wordTrace_append hprefix tailTrace_6761260
  have hstable : (prefixWord ++ tailWord_6761260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761260).length < 2 ^ (prefixWord ++ tailWord_6761260).sum := by decide
  have hdescent : baseEnd_6761260 < baseStart_6761260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761267 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 4]
def baseStart_6761267 : Nat := 118140960795 + 6761267 * 2 ^ 59
def prefixEnd_6761267 : Nat := 4983230072969 + 3 ^ 40 * 6761267 * 2
def baseEnd_6761267 : Nat := 3471779804382903245468005

theorem tailTrace_6761267 : CollatzResearch.WordTrace tailWord_6761267 prefixEnd_6761267 3471779804382903245468005 := by
  unfold tailWord_6761267
  simp only [CollatzResearch.WordTrace]
  refine ⟨246603666796091866315762055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164402444530727910877174703 246603666796091866315762055)
  ·
    refine ⟨369905500194137799473643083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246603666796091866315762055 369905500194137799473643083)
    ·
      refine ⟨554858250291206699210464625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369905500194137799473643083 554858250291206699210464625)
      ·
        refine ⟨416143687718405024407848469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554858250291206699210464625 416143687718405024407848469)
        ·
          refine ⟨19506735361800235519117897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 416143687718405024407848469 19506735361800235519117897)
          ·
            refine ⟨14630051521350176639338423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19506735361800235519117897 14630051521350176639338423)
            ·
              refine ⟨21945077282025264959007635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14630051521350176639338423 21945077282025264959007635)
              ·
                refine ⟨32917615923037897438511453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21945077282025264959007635 32917615923037897438511453)
                ·
                  refine ⟨12344105971139211539441795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32917615923037897438511453 12344105971139211539441795)
                  ·
                    refine ⟨18516158956708817309162693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12344105971139211539441795 18516158956708817309162693)
                    ·
                      refine ⟨3471779804382903245468005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18516158956708817309162693 3471779804382903245468005)
                      ·
                        rfl

theorem cell23_6761267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_6761267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761267 prefixEnd_6761267 := by exact prefixLift 6761267
  have htrace : WordTrace (prefixWord ++ tailWord_6761267) baseStart_6761267 baseEnd_6761267 := by
    simpa [prefixWord, tailWord_6761267, baseEnd_6761267] using wordTrace_append hprefix tailTrace_6761267
  have hstable : (prefixWord ++ tailWord_6761267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761267).length < 2 ^ (prefixWord ++ tailWord_6761267).sum := by decide
  have hdescent : baseEnd_6761267 < baseStart_6761267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761317 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_6761317 : Nat := 118140960795 + 6761317 * 2 ^ 59
def prefixEnd_6761317 : Nat := 4983230072969 + 3 ^ 40 * 6761317 * 2
def baseEnd_6761317 : Nat := 3471805478415628049842775

theorem tailTrace_6761317 : CollatzResearch.WordTrace tailWord_6761317 prefixEnd_6761317 3471805478415628049842775 := by
  unfold tailWord_6761317
  simp only [CollatzResearch.WordTrace]
  refine ⟨246605490445910724855082205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164403660297273816570054803 246605490445910724855082205)
  ·
    refine ⟨92477058917216521820655827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246605490445910724855082205 92477058917216521820655827)
    ·
      refine ⟨138715588375824782730983741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92477058917216521820655827 138715588375824782730983741)
      ·
        refine ⟨52018345640934293524118903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138715588375824782730983741 52018345640934293524118903)
        ·
          refine ⟨78027518461401440286178355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52018345640934293524118903 78027518461401440286178355)
          ·
            refine ⟨117041277692102160429267533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78027518461401440286178355 117041277692102160429267533)
            ·
              refine ⟨43890479134538310160975325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117041277692102160429267533 43890479134538310160975325)
              ·
                refine ⟨16458929675451866310365747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43890479134538310160975325 16458929675451866310365747)
                ·
                  refine ⟨24688394513177799465548621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16458929675451866310365747 24688394513177799465548621)
                  ·
                    refine ⟨9258147942441674799580733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24688394513177799465548621 9258147942441674799580733)
                    ·
                      refine ⟨3471805478415628049842775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258147942441674799580733 3471805478415628049842775)
                      ·
                        rfl

theorem cell23_6761317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_6761317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761317 prefixEnd_6761317 := by exact prefixLift 6761317
  have htrace : WordTrace (prefixWord ++ tailWord_6761317) baseStart_6761317 baseEnd_6761317 := by
    simpa [prefixWord, tailWord_6761317, baseEnd_6761317] using wordTrace_append hprefix tailTrace_6761317
  have hstable : (prefixWord ++ tailWord_6761317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761317).length < 2 ^ (prefixWord ++ tailWord_6761317).sum := by decide
  have hdescent : baseEnd_6761317 < baseStart_6761317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761351 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_6761351 : Nat := 118140960795 + 6761351 * 2 ^ 59
def prefixEnd_6761351 : Nat := 4983230072969 + 3 ^ 40 * 6761351 * 2
def baseEnd_6761351 : Nat := 3471822936757880916817619

theorem tailTrace_6761351 : CollatzResearch.WordTrace tailWord_6761351 prefixEnd_6761351 3471822936757880916817619 := by
  unfold tailWord_6761351
  simp only [CollatzResearch.WordTrace]
  refine ⟨246606730527787548661819907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164404487018525032441213271 246606730527787548661819907)
  ·
    refine ⟨369910095791681322992729861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246606730527787548661819907 369910095791681322992729861)
    ·
      refine ⟨69358142960940248061136849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369910095791681322992729861 69358142960940248061136849)
      ·
        refine ⟨52018607220705186045852637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69358142960940248061136849 52018607220705186045852637)
        ·
          refine ⟨19506977707764444767194739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52018607220705186045852637 19506977707764444767194739)
          ·
            refine ⟨29260466561646667150792109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19506977707764444767194739 29260466561646667150792109)
            ·
              refine ⟨10972674960617500181547041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29260466561646667150792109 10972674960617500181547041)
              ·
                refine ⟨8229506220463125136160281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10972674960617500181547041 8229506220463125136160281)
                ·
                  refine ⟨6172129665347343852120211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8229506220463125136160281 6172129665347343852120211)
                  ·
                    refine ⟨9258194498021015778180317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6172129665347343852120211 9258194498021015778180317)
                    ·
                      refine ⟨3471822936757880916817619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258194498021015778180317 3471822936757880916817619)
                      ·
                        rfl

theorem cell23_6761351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_6761351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761351 prefixEnd_6761351 := by exact prefixLift 6761351
  have htrace : WordTrace (prefixWord ++ tailWord_6761351) baseStart_6761351 baseEnd_6761351 := by
    simpa [prefixWord, tailWord_6761351, baseEnd_6761351] using wordTrace_append hprefix tailTrace_6761351
  have hstable : (prefixWord ++ tailWord_6761351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761351).length < 2 ^ (prefixWord ++ tailWord_6761351).sum := by decide
  have hdescent : baseEnd_6761351 < baseStart_6761351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761378 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_6761378 : Nat := 118140960795 + 6761378 * 2 ^ 59
def prefixEnd_6761378 : Nat := 4983230072969 + 3 ^ 40 * 6761378 * 2
def baseEnd_6761378 : Nat := 3471836800735552311179995

theorem tailTrace_6761378 : CollatzResearch.WordTrace tailWord_6761378 prefixEnd_6761378 3471836800735552311179995 := by
  unfold tailWord_6761378
  simp only [CollatzResearch.WordTrace]
  refine ⟨61651928824672433068263197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164405143532459821515368525 61651928824672433068263197)
  ·
    refine ⟨23119473309252162400598699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61651928824672433068263197 23119473309252162400598699)
    ·
      refine ⟨34679209963878243600898049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23119473309252162400598699 34679209963878243600898049)
      ·
        refine ⟨26009407472908682700673537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34679209963878243600898049 26009407472908682700673537)
        ·
          refine ⟨19507055604681512025505153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26009407472908682700673537 19507055604681512025505153)
          ·
            refine ⟨14630291703511134019128865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19507055604681512025505153 14630291703511134019128865)
            ·
              refine ⟨10972718777633350514346649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14630291703511134019128865 10972718777633350514346649)
              ·
                refine ⟨8229539083225012885759987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10972718777633350514346649 8229539083225012885759987)
                ·
                  refine ⟨12344308624837519328639981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229539083225012885759987 12344308624837519328639981)
                  ·
                    refine ⟨4629115734314069748239993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12344308624837519328639981 4629115734314069748239993)
                    ·
                      refine ⟨3471836800735552311179995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629115734314069748239993 3471836800735552311179995)
                      ·
                        rfl

theorem cell23_6761378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_6761378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761378 prefixEnd_6761378 := by exact prefixLift 6761378
  have htrace : WordTrace (prefixWord ++ tailWord_6761378) baseStart_6761378 baseEnd_6761378 := by
    simpa [prefixWord, tailWord_6761378, baseEnd_6761378] using wordTrace_append hprefix tailTrace_6761378
  have hstable : (prefixWord ++ tailWord_6761378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761378).length < 2 ^ (prefixWord ++ tailWord_6761378).sum := by decide
  have hdescent : baseEnd_6761378 < baseStart_6761378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761407 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 3]
def baseStart_6761407 : Nat := 118140960795 + 6761407 * 2 ^ 59
def prefixEnd_6761407 : Nat := 4983230072969 + 3 ^ 40 * 6761407 * 2
def baseEnd_6761407 : Nat := 3471851691674532697717361

theorem tailTrace_6761407 : CollatzResearch.WordTrace tailWord_6761407 prefixEnd_6761407 3471851691674532697717361 := by
  unfold tailWord_6761407
  simp only [CollatzResearch.WordTrace]
  refine ⟨246608773015584670225858475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164405848677056446817238983 246608773015584670225858475)
  ·
    refine ⟨369913159523377005338787713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246608773015584670225858475 369913159523377005338787713)
    ·
      refine ⟨277434869642532754004090785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369913159523377005338787713 277434869642532754004090785)
      ·
        refine ⟨208076152231899565503068089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277434869642532754004090785 208076152231899565503068089)
        ·
          refine ⟨156057114173924674127301067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208076152231899565503068089 156057114173924674127301067)
          ·
            refine ⟨234085671260887011190951601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156057114173924674127301067 234085671260887011190951601)
            ·
              refine ⟨175564253445665258393213701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234085671260887011190951601 175564253445665258393213701)
              ·
                refine ⟨32918297521062235948727569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175564253445665258393213701 32918297521062235948727569)
                ·
                  refine ⟨24688723140796676961545677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32918297521062235948727569 24688723140796676961545677)
                  ·
                    refine ⟨9258271177798753860579629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24688723140796676961545677 9258271177798753860579629)
                    ·
                      refine ⟨3471851691674532697717361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258271177798753860579629 3471851691674532697717361)
                      ·
                        rfl

theorem cell23_6761407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_6761407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761407 prefixEnd_6761407 := by exact prefixLift 6761407
  have htrace : WordTrace (prefixWord ++ tailWord_6761407) baseStart_6761407 baseEnd_6761407 := by
    simpa [prefixWord, tailWord_6761407, baseEnd_6761407] using wordTrace_append hprefix tailTrace_6761407
  have hstable : (prefixWord ++ tailWord_6761407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761407).length < 2 ^ (prefixWord ++ tailWord_6761407).sum := by decide
  have hdescent : baseEnd_6761407 < baseStart_6761407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761464 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 2, 4, 2]
def baseStart_6761464 : Nat := 118140960795 + 6761464 * 2 ^ 59
def prefixEnd_6761464 : Nat := 4983230072969 + 3 ^ 40 * 6761464 * 2
def baseEnd_6761464 : Nat := 3471880960071838974704599

theorem tailTrace_6761464 : CollatzResearch.WordTrace tailWord_6761464 prefixEnd_6761464 3471880960071838974704599 := by
  unfold tailWord_6761464
  simp only [CollatzResearch.WordTrace]
  refine ⟨123305425988189084480341723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164407234650918779307122297 123305425988189084480341723)
  ·
    refine ⟨184958138982283626720512585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123305425988189084480341723 184958138982283626720512585)
    ·
      refine ⟨138718604236712720040384439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184958138982283626720512585 138718604236712720040384439)
      ·
        refine ⟨208077906355069080060576659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138718604236712720040384439 208077906355069080060576659)
        ·
          refine ⟨312116859532603620090864989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208077906355069080060576659 312116859532603620090864989)
          ·
            refine ⟨117043822324726357534074371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312116859532603620090864989 117043822324726357534074371)
            ·
              refine ⟨175565733487089536301111557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117043822324726357534074371 175565733487089536301111557)
              ·
                refine ⟨32918575028829288056458417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175565733487089536301111557 32918575028829288056458417)
                ·
                  refine ⟨24688931271621966042343813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32918575028829288056458417 24688931271621966042343813)
                  ·
                    refine ⟨4629174613429118632939465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24688931271621966042343813 4629174613429118632939465)
                    ·
                      refine ⟨3471880960071838974704599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629174613429118632939465 3471880960071838974704599)
                      ·
                        rfl

theorem cell23_6761464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_6761464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761464 prefixEnd_6761464 := by exact prefixLift 6761464
  have htrace : WordTrace (prefixWord ++ tailWord_6761464) baseStart_6761464 baseEnd_6761464 := by
    simpa [prefixWord, tailWord_6761464, baseEnd_6761464] using wordTrace_append hprefix tailTrace_6761464
  have hstable : (prefixWord ++ tailWord_6761464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761464).length < 2 ^ (prefixWord ++ tailWord_6761464).sum := by decide
  have hdescent : baseEnd_6761464 < baseStart_6761464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761467 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 3]
def baseStart_6761467 : Nat := 118140960795 + 6761467 * 2 ^ 59
def prefixEnd_6761467 : Nat := 4983230072969 + 3 ^ 40 * 6761467 * 2
def baseEnd_6761467 : Nat := 3471882500513802462967085

theorem tailTrace_6761467 : CollatzResearch.WordTrace tailWord_6761467 prefixEnd_6761467 3471882500513802462967085 := by
  unfold tailWord_6761467
  simp only [CollatzResearch.WordTrace]
  refine ⟨246610961395367300473042655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164407307596911533648695103 246610961395367300473042655)
  ·
    refine ⟨369916442093050950709563983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246610961395367300473042655 369916442093050950709563983)
    ·
      refine ⟨554874663139576426064345975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369916442093050950709563983 554874663139576426064345975)
      ·
        refine ⟨832311994709364639096518963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554874663139576426064345975 832311994709364639096518963)
        ·
          refine ⟨1248467992064046958644778445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832311994709364639096518963 1248467992064046958644778445)
          ·
            refine ⟨468175497024017609491791917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1248467992064046958644778445 468175497024017609491791917)
            ·
              refine ⟨175565811384006603559421969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468175497024017609491791917 175565811384006603559421969)
              ·
                refine ⟨131674358538004952669566477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175565811384006603559421969 131674358538004952669566477)
                ·
                  refine ⟨49377884451751857251087429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131674358538004952669566477 49377884451751857251087429)
                  ·
                    refine ⟨9258353334703473234578893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49377884451751857251087429 9258353334703473234578893)
                    ·
                      refine ⟨3471882500513802462967085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258353334703473234578893 3471882500513802462967085)
                      ·
                        rfl

theorem cell23_6761467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 3].length) (baseStart_6761467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761467 prefixEnd_6761467 := by exact prefixLift 6761467
  have htrace : WordTrace (prefixWord ++ tailWord_6761467) baseStart_6761467 baseEnd_6761467 := by
    simpa [prefixWord, tailWord_6761467, baseEnd_6761467] using wordTrace_append hprefix tailTrace_6761467
  have hstable : (prefixWord ++ tailWord_6761467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761467).length < 2 ^ (prefixWord ++ tailWord_6761467).sum := by decide
  have hdescent : baseEnd_6761467 < baseStart_6761467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761501 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_6761501 : Nat := 118140960795 + 6761501 * 2 ^ 59
def prefixEnd_6761501 : Nat := 4983230072969 + 3 ^ 40 * 6761501 * 2
def baseEnd_6761501 : Nat := 3471899958856055329941929

theorem tailTrace_6761501 : CollatzResearch.WordTrace tailWord_6761501 prefixEnd_6761501 3471899958856055329941929 := by
  unfold tailWord_6761501
  simp only [CollatzResearch.WordTrace]
  refine ⟨246612201477244124279780357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164408134318162749519853571 246612201477244124279780357)
  ·
    refine ⟨46239787776983273302458817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246612201477244124279780357 46239787776983273302458817)
    ·
      refine ⟨34679840832737454976844113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46239787776983273302458817 34679840832737454976844113)
      ·
        refine ⟨26009880624553091232633085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34679840832737454976844113 26009880624553091232633085)
        ·
          refine ⟨9753705234207409212237407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26009880624553091232633085 9753705234207409212237407)
          ·
            refine ⟨14630557851311113818356111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9753705234207409212237407 14630557851311113818356111)
            ·
              refine ⟨21945836776966670727534167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14630557851311113818356111 21945836776966670727534167)
              ·
                refine ⟨32918755165450006091301251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21945836776966670727534167 32918755165450006091301251)
                ·
                  refine ⟨49378132748175009136951877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32918755165450006091301251 49378132748175009136951877)
                  ·
                    refine ⟨9258399890282814213178477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49378132748175009136951877 9258399890282814213178477)
                    ·
                      refine ⟨3471899958856055329941929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258399890282814213178477 3471899958856055329941929)
                      ·
                        rfl

theorem cell23_6761501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_6761501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761501 prefixEnd_6761501 := by exact prefixLift 6761501
  have htrace : WordTrace (prefixWord ++ tailWord_6761501) baseStart_6761501 baseEnd_6761501 := by
    simpa [prefixWord, tailWord_6761501, baseEnd_6761501] using wordTrace_append hprefix tailTrace_6761501
  have hstable : (prefixWord ++ tailWord_6761501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761501).length < 2 ^ (prefixWord ++ tailWord_6761501).sum := by decide
  have hdescent : baseEnd_6761501 < baseStart_6761501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761508 : List Nat := [2, 3, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_6761508 : Nat := 118140960795 + 6761508 * 2 ^ 59
def prefixEnd_6761508 : Nat := 4983230072969 + 3 ^ 40 * 6761508 * 2
def baseEnd_6761508 : Nat := 1157301184406878934184799

theorem tailTrace_6761508 : CollatzResearch.WordTrace tailWord_6761508 prefixEnd_6761508 1157301184406878934184799 := by
  unfold tailWord_6761508
  simp only [CollatzResearch.WordTrace]
  refine ⟨123306228394109382237642589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164408304525479176316856785 123306228394109382237642589)
  ·
    refine ⟨46239835647791018339115971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123306228394109382237642589 46239835647791018339115971)
    ·
      refine ⟨69359753471686527508673957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46239835647791018339115971 69359753471686527508673957)
      ·
        refine ⟨13004953775941223907876367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69359753471686527508673957 13004953775941223907876367)
        ·
          refine ⟨19507430663911835861814551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13004953775941223907876367 19507430663911835861814551)
          ·
            refine ⟨29261145995867753792721827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19507430663911835861814551 29261145995867753792721827)
            ·
              refine ⟨43891718993801630689082741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29261145995867753792721827 43891718993801630689082741)
              ·
                refine ⟨4114848655668902877101507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43891718993801630689082741 4114848655668902877101507)
                ·
                  refine ⟨6172272983503354315652261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114848655668902877101507 6172272983503354315652261)
                  ·
                    refine ⟨1157301184406878934184799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6172272983503354315652261 1157301184406878934184799)
                    ·
                      rfl

theorem cell23_6761508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_6761508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761508 prefixEnd_6761508 := by exact prefixLift 6761508
  have htrace : WordTrace (prefixWord ++ tailWord_6761508) baseStart_6761508 baseEnd_6761508 := by
    simpa [prefixWord, tailWord_6761508, baseEnd_6761508] using wordTrace_append hprefix tailTrace_6761508
  have hstable : (prefixWord ++ tailWord_6761508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761508).length < 2 ^ (prefixWord ++ tailWord_6761508).sum := by decide
  have hdescent : baseEnd_6761508 < baseStart_6761508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761564 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_6761564 : Nat := 118140960795 + 6761564 * 2 ^ 59
def prefixEnd_6761564 : Nat := 4983230072969 + 3 ^ 40 * 6761564 * 2
def baseEnd_6761564 : Nat := 1157310769379096194484713

theorem tailTrace_6761564 : CollatzResearch.WordTrace tailWord_6761564 prefixEnd_6761564 1157310769379096194484713 := by
  unfold tailWord_6761564
  simp only [CollatzResearch.WordTrace]
  refine ⟨123307249638007943019661873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164409666184010590692882497 123307249638007943019661873)
  ·
    refine ⟨92480437228505957264746405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123307249638007943019661873 92480437228505957264746405)
    ·
      refine ⟨17340081980344866987139951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92480437228505957264746405 17340081980344866987139951)
      ·
        refine ⟨26010122970517300480709927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17340081980344866987139951 26010122970517300480709927)
        ·
          refine ⟨39015184455775950721064891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26010122970517300480709927 39015184455775950721064891)
          ·
            refine ⟨58522776683663926081597337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39015184455775950721064891 58522776683663926081597337)
            ·
              refine ⟨43892082512747944561198003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58522776683663926081597337 43892082512747944561198003)
              ·
                refine ⟨65838123769121916841797005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43892082512747944561198003 65838123769121916841797005)
                ·
                  refine ⟨24689296413420718815673877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65838123769121916841797005 24689296413420718815673877)
                  ·
                    refine ⟨1157310769379096194484713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24689296413420718815673877 1157310769379096194484713)
                    ·
                      rfl

theorem cell23_6761564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_6761564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761564 prefixEnd_6761564 := by exact prefixLift 6761564
  have htrace : WordTrace (prefixWord ++ tailWord_6761564) baseStart_6761564 baseEnd_6761564 := by
    simpa [prefixWord, tailWord_6761564, baseEnd_6761564] using wordTrace_append hprefix tailTrace_6761564
  have hstable : (prefixWord ++ tailWord_6761564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761564).length < 2 ^ (prefixWord ++ tailWord_6761564).sum := by decide
  have hdescent : baseEnd_6761564 < baseStart_6761564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761577 : List Nat := [1, 2, 1, 1, 1, 6, 11]
def baseStart_6761577 : Nat := 118140960795 + 6761577 * 2 ^ 59
def prefixEnd_6761577 : Nat := 4983230072969 + 3 ^ 40 * 6761577 * 2
def baseEnd_6761577 : Nat := 42863444239330827562859

theorem tailTrace_6761577 : CollatzResearch.WordTrace tailWord_6761577 prefixEnd_6761577 42863444239330827562859 := by
  unfold tailWord_6761577
  simp only [CollatzResearch.WordTrace]
  refine ⟨246614973424968789259546985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164409982283312526173031323 246614973424968789259546985)
  ·
    refine ⟨184961230068726591944660239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246614973424968789259546985 184961230068726591944660239)
    ·
      refine ⟨277441845103089887916990359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184961230068726591944660239 277441845103089887916990359)
      ·
        refine ⟨416162767654634831875485539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277441845103089887916990359 416162767654634831875485539)
        ·
          refine ⟨624244151481952247813228309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416162767654634831875485539 624244151481952247813228309)
          ·
            refine ⟨29261444600716511616245077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 624244151481952247813228309 29261444600716511616245077)
            ·
              refine ⟨42863444239330827562859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29261444600716511616245077 42863444239330827562859)
              ·
                rfl

theorem cell23_6761577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 11].length) (baseStart_6761577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761577 prefixEnd_6761577 := by exact prefixLift 6761577
  have htrace : WordTrace (prefixWord ++ tailWord_6761577) baseStart_6761577 baseEnd_6761577 := by
    simpa [prefixWord, tailWord_6761577, baseEnd_6761577] using wordTrace_append hprefix tailTrace_6761577
  have hstable : (prefixWord ++ tailWord_6761577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761577).length < 2 ^ (prefixWord ++ tailWord_6761577).sum := by decide
  have hdescent : baseEnd_6761577 < baseStart_6761577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761581 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_6761581 : Nat := 118140960795 + 6761581 * 2 ^ 59
def prefixEnd_6761581 : Nat := 4983230072969 + 3 ^ 40 * 6761581 * 2
def baseEnd_6761581 : Nat := 1157313679102805005647187

theorem tailTrace_6761581 : CollatzResearch.WordTrace tailWord_6761581 prefixEnd_6761581 1157313679102805005647187 := by
  unfold tailWord_6761581
  simp only [CollatzResearch.WordTrace]
  refine ⟨246615119316954297942692597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164410079544636198628461731 246615119316954297942692597)
  ·
    refine ⟨23120167435964465432127431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246615119316954297942692597 23120167435964465432127431)
    ·
      refine ⟨34680251153946698148191147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23120167435964465432127431 34680251153946698148191147)
      ·
        refine ⟨52020376730920047222286721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34680251153946698148191147 52020376730920047222286721)
        ·
          refine ⟨39015282548190035416715041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52020376730920047222286721 39015282548190035416715041)
          ·
            refine ⟨29261461911142526562536281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39015282548190035416715041 29261461911142526562536281)
            ·
              refine ⟨21946096433356894921902211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29261461911142526562536281 21946096433356894921902211)
              ·
                refine ⟨32919144650035342382853317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21946096433356894921902211 32919144650035342382853317)
                ·
                  refine ⟨6172339621881626696784997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32919144650035342382853317 6172339621881626696784997)
                  ·
                    refine ⟨1157313679102805005647187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6172339621881626696784997 1157313679102805005647187)
                    ·
                      rfl

theorem cell23_6761581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_6761581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761581 prefixEnd_6761581 := by exact prefixLift 6761581
  have htrace : WordTrace (prefixWord ++ tailWord_6761581) baseStart_6761581 baseEnd_6761581 := by
    simpa [prefixWord, tailWord_6761581, baseEnd_6761581] using wordTrace_append hprefix tailTrace_6761581
  have hstable : (prefixWord ++ tailWord_6761581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761581).length < 2 ^ (prefixWord ++ tailWord_6761581).sum := by decide
  have hdescent : baseEnd_6761581 < baseStart_6761581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761582 : List Nat := [4, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_6761582 : Nat := 118140960795 + 6761582 * 2 ^ 59
def prefixEnd_6761582 : Nat := 4983230072969 + 3 ^ 40 * 6761582 * 2
def baseEnd_6761582 : Nat := 3471941550789069513029057

theorem tailTrace_6761582 : CollatzResearch.WordTrace tailWord_6761582 prefixEnd_6761582 3471941550789069513029057 := by
  unfold tailWord_6761582
  simp only [CollatzResearch.WordTrace]
  refine ⟨30826894473743834389184875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164410103859967116742319333 30826894473743834389184875)
  ·
    refine ⟨46240341710615751583777313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30826894473743834389184875 46240341710615751583777313)
    ·
      refine ⟨34680256282961813687832985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46240341710615751583777313 34680256282961813687832985)
      ·
        refine ⟨26010192212221360265874739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34680256282961813687832985 26010192212221360265874739)
        ·
          refine ⟨39015288318332040398812109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26010192212221360265874739 39015288318332040398812109)
          ·
            refine ⟨14630733119374515149554541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39015288318332040398812109 14630733119374515149554541)
            ·
              refine ⟨5486524919765443181082953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14630733119374515149554541 5486524919765443181082953)
              ·
                refine ⟨4114893689824082385812215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5486524919765443181082953 4114893689824082385812215)
                ·
                  refine ⟨6172340534736123578718323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114893689824082385812215 6172340534736123578718323)
                  ·
                    refine ⟨9258510802104185368077485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6172340534736123578718323 9258510802104185368077485)
                    ·
                      refine ⟨3471941550789069513029057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258510802104185368077485 3471941550789069513029057)
                      ·
                        rfl

theorem cell23_6761582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_6761582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761582 prefixEnd_6761582 := by exact prefixLift 6761582
  have htrace : WordTrace (prefixWord ++ tailWord_6761582) baseStart_6761582 baseEnd_6761582 := by
    simpa [prefixWord, tailWord_6761582, baseEnd_6761582] using wordTrace_append hprefix tailTrace_6761582
  have hstable : (prefixWord ++ tailWord_6761582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761582).length < 2 ^ (prefixWord ++ tailWord_6761582).sum := by decide
  have hdescent : baseEnd_6761582 < baseStart_6761582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761605 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 1, 1, 4]
def baseStart_6761605 : Nat := 118140960795 + 6761605 * 2 ^ 59
def prefixEnd_6761605 : Nat := 4983230072969 + 3 ^ 40 * 6761605 * 2
def baseEnd_6761605 : Nat := 3471953360844122923041451

theorem tailTrace_6761605 : CollatzResearch.WordTrace tailWord_6761605 prefixEnd_6761605 3471953360844122923041451 := by
  unfold tailWord_6761605
  simp only [CollatzResearch.WordTrace]
  refine ⟨246615994668867350041566269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164410663112578233361044179 246615994668867350041566269)
  ·
    refine ⟨92480998000825256265587351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246615994668867350041566269 92480998000825256265587351)
    ·
      refine ⟨138721497001237884398381027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92480998000825256265587351 138721497001237884398381027)
      ·
        refine ⟨208082245501856826597571541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138721497001237884398381027 208082245501856826597571541)
        ·
          refine ⟨4876927628949769373380583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 208082245501856826597571541 4876927628949769373380583)
          ·
            refine ⟨7315391443424654060070875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876927628949769373380583 7315391443424654060070875)
            ·
              refine ⟨10973087165136981090106313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7315391443424654060070875 10973087165136981090106313)
              ·
                refine ⟨8229815373852735817579735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10973087165136981090106313 8229815373852735817579735)
                ·
                  refine ⟨12344723060779103726369603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229815373852735817579735 12344723060779103726369603)
                  ·
                    refine ⟨18517084591168655589554405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12344723060779103726369603 18517084591168655589554405)
                    ·
                      refine ⟨3471953360844122923041451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18517084591168655589554405 3471953360844122923041451)
                      ·
                        rfl

theorem cell23_6761605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_6761605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761605 prefixEnd_6761605 := by exact prefixLift 6761605
  have htrace : WordTrace (prefixWord ++ tailWord_6761605) baseStart_6761605 baseEnd_6761605 := by
    simpa [prefixWord, tailWord_6761605, baseEnd_6761605] using wordTrace_append hprefix tailTrace_6761605
  have hstable : (prefixWord ++ tailWord_6761605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761605).length < 2 ^ (prefixWord ++ tailWord_6761605).sum := by decide
  have hdescent : baseEnd_6761605 < baseStart_6761605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761608 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6761608 : Nat := 118140960795 + 6761608 * 2 ^ 59
def prefixEnd_6761608 : Nat := 4983230072969 + 3 ^ 40 * 6761608 * 2
def baseEnd_6761608 : Nat := 3471954901286086411303937

theorem tailTrace_6761608 : CollatzResearch.WordTrace tailWord_6761608 prefixEnd_6761608 3471954901286086411303937 := by
  unfold tailWord_6761608
  simp only [CollatzResearch.WordTrace]
  refine ⟨123308052043928240776962739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164410736058570987702616985 123308052043928240776962739)
  ·
    refine ⟨184962078065892361165444109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123308052043928240776962739 184962078065892361165444109)
    ·
      refine ⟨69360779274709635437041541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184962078065892361165444109 69360779274709635437041541)
      ·
        refine ⟨13005146114008056644445289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69360779274709635437041541 13005146114008056644445289)
        ·
          refine ⟨9753859585506042483333967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13005146114008056644445289 9753859585506042483333967)
          ·
            refine ⟨14630789378259063725000951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9753859585506042483333967 14630789378259063725000951)
            ·
              refine ⟨21946184067388595587501427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14630789378259063725000951 21946184067388595587501427)
              ·
                refine ⟨32919276101082893381252141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21946184067388595587501427 32919276101082893381252141)
                ·
                  refine ⟨12344728537906085017969553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32919276101082893381252141 12344728537906085017969553)
                  ·
                    refine ⟨9258546403429563763477165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12344728537906085017969553 9258546403429563763477165)
                    ·
                      refine ⟨3471954901286086411303937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258546403429563763477165 3471954901286086411303937)
                      ·
                        rfl

theorem cell23_6761608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6761608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761608 prefixEnd_6761608 := by exact prefixLift 6761608
  have htrace : WordTrace (prefixWord ++ tailWord_6761608) baseStart_6761608 baseEnd_6761608 := by
    simpa [prefixWord, tailWord_6761608, baseEnd_6761608] using wordTrace_append hprefix tailTrace_6761608
  have hstable : (prefixWord ++ tailWord_6761608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761608).length < 2 ^ (prefixWord ++ tailWord_6761608).sum := by decide
  have hdescent : baseEnd_6761608 < baseStart_6761608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761621 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_6761621 : Nat := 118140960795 + 6761621 * 2 ^ 59
def prefixEnd_6761621 : Nat := 4983230072969 + 3 ^ 40 * 6761621 * 2
def baseEnd_6761621 : Nat := 3471961576534594860441377

theorem tailTrace_6761621 : CollatzResearch.WordTrace tailWord_6761621 prefixEnd_6761621 3471961576534594860441377 := by
  unfold tailWord_6761621
  simp only [CollatzResearch.WordTrace]
  refine ⟨246616578236809384774148717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164411052157872923182765811 246616578236809384774148717)
  ·
    refine ⟨92481216838803519290305769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246616578236809384774148717 92481216838803519290305769)
    ·
      refine ⟨69360912629102639467729327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92481216838803519290305769 69360912629102639467729327)
      ·
        refine ⟨104041368943653959201593991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69360912629102639467729327 104041368943653959201593991)
        ·
          refine ⟨156062053415480938802390987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104041368943653959201593991 156062053415480938802390987)
          ·
            refine ⟨234093080123221408203586481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156062053415480938802390987 234093080123221408203586481)
            ·
              refine ⟨175569810092416056152689861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234093080123221408203586481 175569810092416056152689861)
              ·
                refine ⟨32919339392328010528629349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175569810092416056152689861 32919339392328010528629349)
                ·
                  refine ⟨6172376136061501974118003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32919339392328010528629349 6172376136061501974118003)
                  ·
                    refine ⟨9258564204092252961177005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6172376136061501974118003 9258564204092252961177005)
                    ·
                      refine ⟨3471961576534594860441377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258564204092252961177005 3471961576534594860441377)
                      ·
                        rfl

theorem cell23_6761621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_6761621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761621 prefixEnd_6761621 := by exact prefixLift 6761621
  have htrace : WordTrace (prefixWord ++ tailWord_6761621) baseStart_6761621 baseEnd_6761621 := by
    simpa [prefixWord, tailWord_6761621, baseEnd_6761621] using wordTrace_append hprefix tailTrace_6761621
  have hstable : (prefixWord ++ tailWord_6761621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761621).length < 2 ^ (prefixWord ++ tailWord_6761621).sum := by decide
  have hdescent : baseEnd_6761621 < baseStart_6761621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761639 : List Nat := [1, 1, 6, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_6761639 : Nat := 118140960795 + 6761639 * 2 ^ 59
def prefixEnd_6761639 : Nat := 4983230072969 + 3 ^ 40 * 6761639 * 2
def baseEnd_6761639 : Nat := 3471970819186375790016295

theorem tailTrace_6761639 : CollatzResearch.WordTrace tailWord_6761639 prefixEnd_6761639 3471970819186375790016295 := by
  unfold tailWord_6761639
  simp only [CollatzResearch.WordTrace]
  refine ⟨246617234750744173848303971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164411489833829449232202647 246617234750744173848303971)
  ·
    refine ⟨369925852126116260772455957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246617234750744173848303971 369925852126116260772455957)
    ·
      refine ⟨17340274318411699723708873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 369925852126116260772455957 17340274318411699723708873)
      ·
        refine ⟨13005205738808774792781655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17340274318411699723708873 13005205738808774792781655)
        ·
          refine ⟨19507808608213162189172483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13005205738808774792781655 19507808608213162189172483)
          ·
            refine ⟨29261712912319743283758725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19507808608213162189172483 29261712912319743283758725)
            ·
              refine ⟨5486571171059951865704761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29261712912319743283758725 5486571171059951865704761)
              ·
                refine ⟨4114928378294963899278571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5486571171059951865704761 4114928378294963899278571)
                ·
                  refine ⟨6172392567442445848917857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114928378294963899278571 6172392567442445848917857)
                  ·
                    refine ⟨4629294425581834386688393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6172392567442445848917857 4629294425581834386688393)
                    ·
                      refine ⟨3471970819186375790016295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629294425581834386688393 3471970819186375790016295)
                      ·
                        rfl

theorem cell23_6761639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_6761639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761639 prefixEnd_6761639 := by exact prefixLift 6761639
  have htrace : WordTrace (prefixWord ++ tailWord_6761639) baseStart_6761639 baseEnd_6761639 := by
    simpa [prefixWord, tailWord_6761639, baseEnd_6761639] using wordTrace_append hprefix tailTrace_6761639
  have hstable : (prefixWord ++ tailWord_6761639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761639).length < 2 ^ (prefixWord ++ tailWord_6761639).sum := by decide
  have hdescent : baseEnd_6761639 < baseStart_6761639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761665 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_6761665 : Nat := 118140960795 + 6761665 * 2 ^ 59
def prefixEnd_6761665 : Nat := 4983230072969 + 3 ^ 40 * 6761665 * 2
def baseEnd_6761665 : Nat := 3471984169683392688291175

theorem tailTrace_6761665 : CollatzResearch.WordTrace tailWord_6761665 prefixEnd_6761665 3471984169683392688291175 := by
  unfold tailWord_6761665
  simp only [CollatzResearch.WordTrace]
  refine ⟨246618183048649980288750449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164412122032433320192500299 246618183048649980288750449)
  ·
    refine ⟨184963637286487485216562837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246618183048649980288750449 184963637286487485216562837)
    ·
      refine ⟨8670170497804100869526383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184963637286487485216562837 8670170497804100869526383)
      ·
        refine ⟨13005255746706151304289575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8670170497804100869526383 13005255746706151304289575)
        ·
          refine ⟨19507883620059226956434363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13005255746706151304289575 19507883620059226956434363)
          ·
            refine ⟨29261825430088840434651545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19507883620059226956434363 29261825430088840434651545)
            ·
              refine ⟨21946369072566630325988659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29261825430088840434651545 21946369072566630325988659)
              ·
                refine ⟨32919553608849945488982989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21946369072566630325988659 32919553608849945488982989)
                ·
                  refine ⟨12344832603318729558368621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32919553608849945488982989 12344832603318729558368621)
                  ·
                    refine ⟨4629312226244523584388233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12344832603318729558368621 4629312226244523584388233)
                    ·
                      refine ⟨3471984169683392688291175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629312226244523584388233 3471984169683392688291175)
                      ·
                        rfl

theorem cell23_6761665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_6761665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761665 prefixEnd_6761665 := by exact prefixLift 6761665
  have htrace : WordTrace (prefixWord ++ tailWord_6761665) baseStart_6761665 baseEnd_6761665 := by
    simpa [prefixWord, tailWord_6761665, baseEnd_6761665] using wordTrace_append hprefix tailTrace_6761665
  have hstable : (prefixWord ++ tailWord_6761665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761665).length < 2 ^ (prefixWord ++ tailWord_6761665).sum := by decide
  have hdescent : baseEnd_6761665 < baseStart_6761665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761695 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 2, 2, 2]
def baseStart_6761695 : Nat := 118140960795 + 6761695 * 2 ^ 59
def prefixEnd_6761695 : Nat := 4983230072969 + 3 ^ 40 * 6761695 * 2
def baseEnd_6761695 : Nat := 3471999574103027570916037

theorem tailTrace_6761695 : CollatzResearch.WordTrace tailWord_6761695 prefixEnd_6761695 3471999574103027570916037 := by
  unfold tailWord_6761695
  simp only [CollatzResearch.WordTrace]
  refine ⟨246619277238541295412342539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164412851492360863608228359 246619277238541295412342539)
  ·
    refine ⟨369928915857811943118513809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246619277238541295412342539 369928915857811943118513809)
    ·
      refine ⟨277446686893358957338885357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369928915857811943118513809 277446686893358957338885357)
      ·
        refine ⟨104042507585009609002082009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277446686893358957338885357 104042507585009609002082009)
        ·
          refine ⟨78031880688757206751561507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104042507585009609002082009 78031880688757206751561507)
          ·
            refine ⟨117047821033135810127342261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78031880688757206751561507 117047821033135810127342261)
            ·
              refine ⟨10973233221856482199438337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117047821033135810127342261 10973233221856482199438337)
              ·
                refine ⟨8229924916392361649578753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10973233221856482199438337 8229924916392361649578753)
                ·
                  refine ⟨6172443687294271237184065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8229924916392361649578753 6172443687294271237184065)
                  ·
                    refine ⟨4629332765470703427888049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6172443687294271237184065 4629332765470703427888049)
                    ·
                      refine ⟨3471999574103027570916037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629332765470703427888049 3471999574103027570916037)
                      ·
                        rfl

theorem cell23_6761695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_6761695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761695 prefixEnd_6761695 := by exact prefixLift 6761695
  have htrace : WordTrace (prefixWord ++ tailWord_6761695) baseStart_6761695 baseEnd_6761695 := by
    simpa [prefixWord, tailWord_6761695, baseEnd_6761695] using wordTrace_append hprefix tailTrace_6761695
  have hstable : (prefixWord ++ tailWord_6761695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761695).length < 2 ^ (prefixWord ++ tailWord_6761695).sum := by decide
  have hdescent : baseEnd_6761695 < baseStart_6761695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761716 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6761716 : Nat := 118140960795 + 6761716 * 2 ^ 59
def prefixEnd_6761716 : Nat := 4983230072969 + 3 ^ 40 * 6761716 * 2
def baseEnd_6761716 : Nat := 3472010357196771988753441

theorem tailTrace_6761716 : CollatzResearch.WordTrace tailWord_6761716 prefixEnd_6761716 3472010357196771988753441 := by
  unfold tailWord_6761716
  simp only [CollatzResearch.WordTrace]
  refine ⟨123310021585732607999428501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164413362114310143999238001 123310021585732607999428501)
  ·
    refine ⟨5780157261831215999973211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123310021585732607999428501 5780157261831215999973211)
    ·
      refine ⟨8670235892746823999959817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5780157261831215999973211 8670235892746823999959817)
      ·
        refine ⟨6502676919560117999969863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8670235892746823999959817 6502676919560117999969863)
        ·
          refine ⟨9754015379340176999954795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502676919560117999969863 9754015379340176999954795)
          ·
            refine ⟨14631023069010265499932193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754015379340176999954795 14631023069010265499932193)
            ·
              refine ⟨10973267301757699124949145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14631023069010265499932193 10973267301757699124949145)
              ·
                refine ⟨8229950476318274343711859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10973267301757699124949145 8229950476318274343711859)
                ·
                  refine ⟨12344925714477411515567789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229950476318274343711859 12344925714477411515567789)
                  ·
                    refine ⟨4629347142929029318337921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12344925714477411515567789 4629347142929029318337921)
                    ·
                      refine ⟨3472010357196771988753441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629347142929029318337921 3472010357196771988753441)
                      ·
                        rfl

theorem cell23_6761716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6761716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761716 prefixEnd_6761716 := by exact prefixLift 6761716
  have htrace : WordTrace (prefixWord ++ tailWord_6761716) baseStart_6761716 baseEnd_6761716 := by
    simpa [prefixWord, tailWord_6761716, baseEnd_6761716] using wordTrace_append hprefix tailTrace_6761716
  have hstable : (prefixWord ++ tailWord_6761716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761716).length < 2 ^ (prefixWord ++ tailWord_6761716).sum := by decide
  have hdescent : baseEnd_6761716 < baseStart_6761716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761782 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_6761782 : Nat := 118140960795 + 6761782 * 2 ^ 59
def prefixEnd_6761782 : Nat := 4983230072969 + 3 ^ 40 * 6761782 * 2
def baseEnd_6761782 : Nat := 1157348082306656243509379

theorem tailTrace_6761782 : CollatzResearch.WordTrace tailWord_6761782 prefixEnd_6761782 1157348082306656243509379 := by
  unfold tailWord_6761782
  simp only [CollatzResearch.WordTrace]
  refine ⟨15413903149326631829422475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 164414966926150739513839733 15413903149326631829422475)
  ·
    refine ⟨23120854723989947744133713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15413903149326631829422475 23120854723989947744133713)
    ·
      refine ⟨17340641042992460808100285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23120854723989947744133713 17340641042992460808100285)
      ·
        refine ⟨6502740391122172803037607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17340641042992460808100285 6502740391122172803037607)
        ·
          refine ⟨9754110586683259204556411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502740391122172803037607 9754110586683259204556411)
          ·
            refine ⟨14631165880024888806834617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754110586683259204556411 14631165880024888806834617)
            ·
              refine ⟨10973374410018666605125963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14631165880024888806834617 10973374410018666605125963)
              ·
                refine ⟨16460061615027999907688945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10973374410018666605125963 16460061615027999907688945)
                ·
                  refine ⟨12345046211270999930766709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16460061615027999907688945 12345046211270999930766709)
                  ·
                    refine ⟨1157348082306656243509379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12345046211270999930766709 1157348082306656243509379)
                    ·
                      rfl

theorem cell23_6761782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_6761782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761782 prefixEnd_6761782 := by exact prefixLift 6761782
  have htrace : WordTrace (prefixWord ++ tailWord_6761782) baseStart_6761782 baseEnd_6761782 := by
    simpa [prefixWord, tailWord_6761782, baseEnd_6761782] using wordTrace_append hprefix tailTrace_6761782
  have hstable : (prefixWord ++ tailWord_6761782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761782).length < 2 ^ (prefixWord ++ tailWord_6761782).sum := by decide
  have hdescent : baseEnd_6761782 < baseStart_6761782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761785 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 4]
def baseStart_6761785 : Nat := 118140960795 + 6761785 * 2 ^ 59
def prefixEnd_6761785 : Nat := 4983230072969 + 3 ^ 40 * 6761785 * 2
def baseEnd_6761785 : Nat := 3472045787361932218790623

theorem tailTrace_6761785 : CollatzResearch.WordTrace tailWord_6761785 prefixEnd_6761785 3472045787361932218790623 := by
  unfold tailWord_6761785
  simp only [CollatzResearch.WordTrace]
  refine ⟨246622559808215240783118809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164415039872143493855412539 246622559808215240783118809)
  ·
    refine ⟨184966919856161430587339107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246622559808215240783118809 184966919856161430587339107)
    ·
      refine ⟨277450379784242145881008661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184966919856161430587339107 277450379784242145881008661)
      ·
        refine ⟨13005486552386350588172281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 277450379784242145881008661 13005486552386350588172281)
        ·
          refine ⟨9754114914289762941129211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13005486552386350588172281 9754114914289762941129211)
          ·
            refine ⟨14631172371434644411693817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754114914289762941129211 14631172371434644411693817)
            ·
              refine ⟨10973379278575983308770363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14631172371434644411693817 10973379278575983308770363)
              ·
                refine ⟨16460068917863974963155545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10973379278575983308770363 16460068917863974963155545)
                ·
                  refine ⟨12345051688397981222366659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16460068917863974963155545 12345051688397981222366659)
                  ·
                    refine ⟨18517577532596971833549989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12345051688397981222366659 18517577532596971833549989)
                    ·
                      refine ⟨3472045787361932218790623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18517577532596971833549989 3472045787361932218790623)
                      ·
                        rfl

theorem cell23_6761785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_6761785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761785 prefixEnd_6761785 := by exact prefixLift 6761785
  have htrace : WordTrace (prefixWord ++ tailWord_6761785) baseStart_6761785 baseEnd_6761785 := by
    simpa [prefixWord, tailWord_6761785, baseEnd_6761785] using wordTrace_append hprefix tailTrace_6761785
  have hstable : (prefixWord ++ tailWord_6761785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761785).length < 2 ^ (prefixWord ++ tailWord_6761785).sum := by decide
  have hdescent : baseEnd_6761785 < baseStart_6761785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761788 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_6761788 : Nat := 118140960795 + 6761788 * 2 ^ 59
def prefixEnd_6761788 : Nat := 4983230072969 + 3 ^ 40 * 6761788 * 2
def baseEnd_6761788 : Nat := 3472047327803895707053109

theorem tailTrace_6761788 : CollatzResearch.WordTrace tailWord_6761788 prefixEnd_6761788 3472047327803895707053109 := by
  unfold tailWord_6761788
  simp only [CollatzResearch.WordTrace]
  refine ⟨123311334613602186147739009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164415112818136248196985345 123311334613602186147739009)
  ·
    refine ⟨92483500960201639610804257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123311334613602186147739009 92483500960201639610804257)
    ·
      refine ⟨69362625720151229708103193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92483500960201639610804257 69362625720151229708103193)
      ·
        refine ⟨52021969290113422281077395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69362625720151229708103193 52021969290113422281077395)
        ·
          refine ⟨78032953935170133421616093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52021969290113422281077395 78032953935170133421616093)
          ·
            refine ⟨29262357725688800033106035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78032953935170133421616093 29262357725688800033106035)
            ·
              refine ⟨43893536588533200049659053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29262357725688800033106035 43893536588533200049659053)
              ·
                refine ⟨16460076220699950018622145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43893536588533200049659053 16460076220699950018622145)
                ·
                  refine ⟨12345057165524962513966609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16460076220699950018622145 12345057165524962513966609)
                  ·
                    refine ⟨9258792874143721885474957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12345057165524962513966609 9258792874143721885474957)
                    ·
                      refine ⟨3472047327803895707053109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258792874143721885474957 3472047327803895707053109)
                      ·
                        rfl

theorem cell23_6761788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_6761788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761788 prefixEnd_6761788 := by exact prefixLift 6761788
  have htrace : WordTrace (prefixWord ++ tailWord_6761788) baseStart_6761788 baseEnd_6761788 := by
    simpa [prefixWord, tailWord_6761788, baseEnd_6761788] using wordTrace_append hprefix tailTrace_6761788
  have hstable : (prefixWord ++ tailWord_6761788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761788).length < 2 ^ (prefixWord ++ tailWord_6761788).sum := by decide
  have hdescent : baseEnd_6761788 < baseStart_6761788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761851 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 1, 6]
def baseStart_6761851 : Nat := 118140960795 + 6761851 * 2 ^ 59
def prefixEnd_6761851 : Nat := 4983230072969 + 3 ^ 40 * 6761851 * 2
def baseEnd_6761851 : Nat := 1157359892361709653521773

theorem tailTrace_6761851 : CollatzResearch.WordTrace tailWord_6761851 prefixEnd_6761851 1157359892361709653521773 := by
  unfold tailWord_6761851
  simp only [CollatzResearch.WordTrace]
  refine ⟨246624967025976134055021407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164416644683984089370014271 246624967025976134055021407)
  ·
    refine ⟨369937450538964201082532111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246624967025976134055021407 369937450538964201082532111)
    ·
      refine ⟨554906175808446301623798167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369937450538964201082532111 554906175808446301623798167)
      ·
        refine ⟨832359263712669452435697251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554906175808446301623798167 832359263712669452435697251)
        ·
          refine ⟨1248538895569004178653545877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832359263712669452435697251 1248538895569004178653545877)
          ·
            refine ⟨58525260729797070874384963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1248538895569004178653545877 58525260729797070874384963)
            ·
              refine ⟨87787891094695606311577445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58525260729797070874384963 87787891094695606311577445)
              ·
                refine ⟨16460229580255426183420771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87787891094695606311577445 16460229580255426183420771)
                ·
                  refine ⟨24690344370383139275131157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16460229580255426183420771 24690344370383139275131157)
                  ·
                    refine ⟨1157359892361709653521773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24690344370383139275131157 1157359892361709653521773)
                    ·
                      rfl

theorem cell23_6761851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 6].length) (baseStart_6761851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761851 prefixEnd_6761851 := by exact prefixLift 6761851
  have htrace : WordTrace (prefixWord ++ tailWord_6761851) baseStart_6761851 baseEnd_6761851 := by
    simpa [prefixWord, tailWord_6761851, baseEnd_6761851] using wordTrace_append hprefix tailTrace_6761851
  have hstable : (prefixWord ++ tailWord_6761851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761851).length < 2 ^ (prefixWord ++ tailWord_6761851).sum := by decide
  have hdescent : baseEnd_6761851 < baseStart_6761851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761852 : List Nat := [2, 2, 2, 1, 1, 1, 6, 3, 1, 1, 3]
def baseStart_6761852 : Nat := 118140960795 + 6761852 * 2 ^ 59
def prefixEnd_6761852 : Nat := 4983230072969 + 3 ^ 40 * 6761852 * 2
def baseEnd_6761852 : Nat := 3472080190565783456652815

theorem tailTrace_6761852 : CollatzResearch.WordTrace tailWord_6761852 prefixEnd_6761852 3472080190565783456652815 := by
  unfold tailWord_6761852
  simp only [CollatzResearch.WordTrace]
  refine ⟨123312501749486255612903905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164416668999315007483871873 123312501749486255612903905)
  ·
    refine ⟨92484376312114691709677929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123312501749486255612903905 92484376312114691709677929)
    ·
      refine ⟨69363282234086018782258447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92484376312114691709677929 69363282234086018782258447)
      ·
        refine ⟨104044923351129028173387671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69363282234086018782258447 104044923351129028173387671)
        ·
          refine ⟨156067385026693542260081507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104044923351129028173387671 156067385026693542260081507)
          ·
            refine ⟨234101077540040313390122261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156067385026693542260081507 234101077540040313390122261)
            ·
              refine ⟨10973488009689389690161981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234101077540040313390122261 10973488009689389690161981)
              ·
                refine ⟨4115058003633521133810743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10973488009689389690161981 4115058003633521133810743)
                ·
                  refine ⟨6172587005450281700716115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115058003633521133810743 6172587005450281700716115)
                  ·
                    refine ⟨9258880508175422551074173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6172587005450281700716115 9258880508175422551074173)
                    ·
                      refine ⟨3472080190565783456652815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9258880508175422551074173 3472080190565783456652815)
                      ·
                        rfl

theorem cell23_6761852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_6761852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761852 prefixEnd_6761852 := by exact prefixLift 6761852
  have htrace : WordTrace (prefixWord ++ tailWord_6761852) baseStart_6761852 baseEnd_6761852 := by
    simpa [prefixWord, tailWord_6761852, baseEnd_6761852] using wordTrace_append hprefix tailTrace_6761852
  have hstable : (prefixWord ++ tailWord_6761852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761852).length < 2 ^ (prefixWord ++ tailWord_6761852).sum := by decide
  have hdescent : baseEnd_6761852 < baseStart_6761852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761868 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_6761868 : Nat := 118140960795 + 6761868 * 2 ^ 59
def prefixEnd_6761868 : Nat := 4983230072969 + 3 ^ 40 * 6761868 * 2
def baseEnd_6761868 : Nat := 1157362802085418464684247

theorem tailTrace_6761868 : CollatzResearch.WordTrace tailWord_6761868 prefixEnd_6761868 1157362802085418464684247 := by
  unfold tailWord_6761868
  simp only [CollatzResearch.WordTrace]
  refine ⟨123312793533457272979195129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164417058044609697305593505 123312793533457272979195129)
  ·
    refine ⟨92484595150092954734396347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123312793533457272979195129 92484595150092954734396347)
    ·
      refine ⟨138726892725139432101594521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92484595150092954734396347 138726892725139432101594521)
      ·
        refine ⟨104045169543854574076195891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138726892725139432101594521 104045169543854574076195891)
        ·
          refine ⟨156067754315781861114293837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104045169543854574076195891 156067754315781861114293837)
          ·
            refine ⟨58525407868418197917860189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156067754315781861114293837 58525407868418197917860189)
            ·
              refine ⟨21947027950656824219197571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58525407868418197917860189 21947027950656824219197571)
              ·
                refine ⟨32920541925985236328796357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21947027950656824219197571 32920541925985236328796357)
                ·
                  refine ⟨6172601611122231811649317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32920541925985236328796357 6172601611122231811649317)
                  ·
                    refine ⟨1157362802085418464684247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6172601611122231811649317 1157362802085418464684247)
                    ·
                      rfl

theorem cell23_6761868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_6761868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761868 prefixEnd_6761868 := by exact prefixLift 6761868
  have htrace : WordTrace (prefixWord ++ tailWord_6761868) baseStart_6761868 baseEnd_6761868 := by
    simpa [prefixWord, tailWord_6761868, baseEnd_6761868] using wordTrace_append hprefix tailTrace_6761868
  have hstable : (prefixWord ++ tailWord_6761868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761868).length < 2 ^ (prefixWord ++ tailWord_6761868).sum := by decide
  have hdescent : baseEnd_6761868 < baseStart_6761868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761885 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_6761885 : Nat := 118140960795 + 6761885 * 2 ^ 59
def prefixEnd_6761885 : Nat := 4983230072969 + 3 ^ 40 * 6761885 * 2
def baseEnd_6761885 : Nat := 1157365711809127275846721

theorem tailTrace_6761885 : CollatzResearch.WordTrace tailWord_6761885 prefixEnd_6761885 1157365711809127275846721 := by
  unfold tailWord_6761885
  simp only [CollatzResearch.WordTrace]
  refine ⟨246626207107852957861759109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164417471405235305241172739 246626207107852957861759109)
  ·
    refine ⟨46242413832722429599079833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246626207107852957861759109 46242413832722429599079833)
    ·
      refine ⟨34681810374541822199309875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46242413832722429599079833 34681810374541822199309875)
      ·
        refine ⟨52022715561812733298964813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34681810374541822199309875 52022715561812733298964813)
        ·
          refine ⟨19508518335679774987111805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52022715561812733298964813 19508518335679774987111805)
          ·
            refine ⟨7315694375879915620166927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19508518335679774987111805 7315694375879915620166927)
            ·
              refine ⟨10973541563819873430250391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7315694375879915620166927 10973541563819873430250391)
              ·
                refine ⟨16460312345729810145375587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10973541563819873430250391 16460312345729810145375587)
                ·
                  refine ⟨24690468518594715218063381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16460312345729810145375587 24690468518594715218063381)
                  ·
                    refine ⟨1157365711809127275846721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24690468518594715218063381 1157365711809127275846721)
                    ·
                      rfl

theorem cell23_6761885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_6761885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761885 prefixEnd_6761885 := by exact prefixLift 6761885
  have htrace : WordTrace (prefixWord ++ tailWord_6761885) baseStart_6761885 baseEnd_6761885 := by
    simpa [prefixWord, tailWord_6761885, baseEnd_6761885] using wordTrace_append hprefix tailTrace_6761885
  have hstable : (prefixWord ++ tailWord_6761885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761885).length < 2 ^ (prefixWord ++ tailWord_6761885).sum := by decide
  have hdescent : baseEnd_6761885 < baseStart_6761885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761961 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_6761961 : Nat := 118140960795 + 6761961 * 2 ^ 59
def prefixEnd_6761961 : Nat := 4983230072969 + 3 ^ 40 * 6761961 * 2
def baseEnd_6761961 : Nat := 3472136159957123530189813

theorem tailTrace_6761961 : CollatzResearch.WordTrace tailWord_6761961 prefixEnd_6761961 3472136159957123530189813 := by
  unfold tailWord_6761961
  simp only [CollatzResearch.WordTrace]
  refine ⟨246628979055577622841525737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164419319370385081894350491 246628979055577622841525737)
  ·
    refine ⟨184971734291683217131144303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246628979055577622841525737 184971734291683217131144303)
    ·
      refine ⟨277457601437524825696716455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184971734291683217131144303 277457601437524825696716455)
      ·
        refine ⟨416186402156287238545074683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277457601437524825696716455 416186402156287238545074683)
        ·
          refine ⟨624279603234430857817612025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416186402156287238545074683 624279603234430857817612025)
          ·
            refine ⟨468209702425823143363209019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624279603234430857817612025 468209702425823143363209019)
            ·
              refine ⟨702314553638734715044813529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468209702425823143363209019 702314553638734715044813529)
              ·
                refine ⟨526735915229051036283610147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702314553638734715044813529 526735915229051036283610147)
                ·
                  refine ⟨790103872843576554425415221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 526735915229051036283610147 790103872843576554425415221)
                  ·
                    refine ⟨74072238079085301977382677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 790103872843576554425415221 74072238079085301977382677)
                    ·
                      refine ⟨3472136159957123530189813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74072238079085301977382677 3472136159957123530189813)
                      ·
                        rfl

theorem cell23_6761961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_6761961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761961 prefixEnd_6761961 := by exact prefixLift 6761961
  have htrace : WordTrace (prefixWord ++ tailWord_6761961) baseStart_6761961 baseEnd_6761961 := by
    simpa [prefixWord, tailWord_6761961, baseEnd_6761961] using wordTrace_append hprefix tailTrace_6761961
  have hstable : (prefixWord ++ tailWord_6761961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761961).length < 2 ^ (prefixWord ++ tailWord_6761961).sum := by decide
  have hdescent : baseEnd_6761961 < baseStart_6761961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761968 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_6761968 : Nat := 118140960795 + 6761968 * 2 ^ 59
def prefixEnd_6761968 : Nat := 4983230072969 + 3 ^ 40 * 6761968 * 2
def baseEnd_6761968 : Nat := 3472139754321705002802281

theorem tailTrace_6761968 : CollatzResearch.WordTrace tailWord_6761968 prefixEnd_6761968 3472139754321705002802281 := by
  unfold tailWord_6761968
  simp only [CollatzResearch.WordTrace]
  refine ⟨123314617183276131518515279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164419489577701508691353705 123314617183276131518515279)
  ·
    refine ⟨184971925774914197277772919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123314617183276131518515279 184971925774914197277772919)
    ·
      refine ⟨277457888662371295916659379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184971925774914197277772919 277457888662371295916659379)
      ·
        refine ⟨416186832993556943874989069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277457888662371295916659379 416186832993556943874989069)
        ·
          refine ⟨156070062372583853953120901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416186832993556943874989069 156070062372583853953120901)
          ·
            refine ⟨29263136694859472616210169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156070062372583853953120901 29263136694859472616210169)
            ·
              refine ⟨21947352521144604462157627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29263136694859472616210169 21947352521144604462157627)
              ·
                refine ⟨32921028781716906693236441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21947352521144604462157627 32921028781716906693236441)
                ·
                  refine ⟨24690771586287680019927331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32921028781716906693236441 24690771586287680019927331)
                  ·
                    refine ⟨37036157379431520029890997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24690771586287680019927331 37036157379431520029890997)
                    ·
                      refine ⟨3472139754321705002802281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37036157379431520029890997 3472139754321705002802281)
                      ·
                        rfl

theorem cell23_6761968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_6761968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761968 prefixEnd_6761968 := by exact prefixLift 6761968
  have htrace : WordTrace (prefixWord ++ tailWord_6761968) baseStart_6761968 baseEnd_6761968 := by
    simpa [prefixWord, tailWord_6761968, baseEnd_6761968] using wordTrace_append hprefix tailTrace_6761968
  have hstable : (prefixWord ++ tailWord_6761968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761968).length < 2 ^ (prefixWord ++ tailWord_6761968).sum := by decide
  have hdescent : baseEnd_6761968 < baseStart_6761968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761969 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 1, 3, 2]
def baseStart_6761969 : Nat := 118140960795 + 6761969 * 2 ^ 59
def prefixEnd_6761969 : Nat := 4983230072969 + 3 ^ 40 * 6761969 * 2
def baseEnd_6761969 : Nat := 3472140267802359498889777

theorem tailTrace_6761969 : CollatzResearch.WordTrace tailWord_6761969 prefixEnd_6761969 3472140267802359498889777 := by
  unfold tailWord_6761969
  simp only [CollatzResearch.WordTrace]
  refine ⟨246629270839548640207816961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164419513893032426805211307 246629270839548640207816961)
  ·
    refine ⟨184971953129661480155862721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246629270839548640207816961 184971953129661480155862721)
    ·
      refine ⟨138728964847246110116897041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184971953129661480155862721 138728964847246110116897041)
      ·
        refine ⟨104046723635434582587672781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138728964847246110116897041 104046723635434582587672781)
        ·
          refine ⟨39017521363287968470377293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104046723635434582587672781 39017521363287968470377293)
          ·
            refine ⟨14631570511232988176391485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39017521363287968470377293 14631570511232988176391485)
            ·
              refine ⟨5486838941712370566146807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14631570511232988176391485 5486838941712370566146807)
              ·
                refine ⟨8230258412568555849220211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5486838941712370566146807 8230258412568555849220211)
                ·
                  refine ⟨12345387618852833773830317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8230258412568555849220211 12345387618852833773830317)
                  ·
                    refine ⟨4629520357069812665186369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12345387618852833773830317 4629520357069812665186369)
                    ·
                      refine ⟨3472140267802359498889777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629520357069812665186369 3472140267802359498889777)
                      ·
                        rfl

theorem cell23_6761969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_6761969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761969 prefixEnd_6761969 := by exact prefixLift 6761969
  have htrace : WordTrace (prefixWord ++ tailWord_6761969) baseStart_6761969 baseEnd_6761969 := by
    simpa [prefixWord, tailWord_6761969, baseEnd_6761969] using wordTrace_append hprefix tailTrace_6761969
  have hstable : (prefixWord ++ tailWord_6761969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761969).length < 2 ^ (prefixWord ++ tailWord_6761969).sum := by decide
  have hdescent : baseEnd_6761969 < baseStart_6761969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761971 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 11]
def baseStart_6761971 : Nat := 118140960795 + 6761971 * 2 ^ 59
def prefixEnd_6761971 : Nat := 4983230072969 + 3 ^ 40 * 6761971 * 2
def baseEnd_6761971 : Nat := 385793477195963165673863

theorem tailTrace_6761971 : CollatzResearch.WordTrace tailWord_6761971 prefixEnd_6761971 385793477195963165673863 := by
  unfold tailWord_6761971
  simp only [CollatzResearch.WordTrace]
  refine ⟨246629343785541394549389767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164419562523694263032926511 246629343785541394549389767)
  ·
    refine ⟨369944015678312091824084651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246629343785541394549389767 369944015678312091824084651)
    ·
      refine ⟨554916023517468137736126977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369944015678312091824084651 554916023517468137736126977)
      ·
        refine ⟨416187017638101103302095233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554916023517468137736126977 416187017638101103302095233)
        ·
          refine ⟨312140263228575827476571425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416187017638101103302095233 312140263228575827476571425)
          ·
            refine ⟨234105197421431870607428569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312140263228575827476571425 234105197421431870607428569)
            ·
              refine ⟨175578898066073902955571427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234105197421431870607428569 175578898066073902955571427)
              ·
                refine ⟨263368347099110854433357141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175578898066073902955571427 263368347099110854433357141)
                ·
                  refine ⟨385793477195963165673863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 263368347099110854433357141 385793477195963165673863)
                  ·
                    rfl

theorem cell23_6761971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 11].length) (baseStart_6761971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761971 prefixEnd_6761971 := by exact prefixLift 6761971
  have htrace : WordTrace (prefixWord ++ tailWord_6761971) baseStart_6761971 baseEnd_6761971 := by
    simpa [prefixWord, tailWord_6761971, baseEnd_6761971] using wordTrace_append hprefix tailTrace_6761971
  have hstable : (prefixWord ++ tailWord_6761971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761971).length < 2 ^ (prefixWord ++ tailWord_6761971).sum := by decide
  have hdescent : baseEnd_6761971 < baseStart_6761971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761978 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_6761978 : Nat := 118140960795 + 6761978 * 2 ^ 59
def prefixEnd_6761978 : Nat := 4983230072969 + 3 ^ 40 * 6761978 * 2
def baseEnd_6761978 : Nat := 3472144889128249963677235

theorem tailTrace_6761978 : CollatzResearch.WordTrace tailWord_6761978 prefixEnd_6761978 3472144889128249963677235 := by
  unfold tailWord_6761978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61657399774129008686223647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164419732731010689829929725 61657399774129008686223647)
  ·
    refine ⟨92486099661193513029335471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61657399774129008686223647 92486099661193513029335471)
    ·
      refine ⟨138729149491790269544003207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92486099661193513029335471 138729149491790269544003207)
      ·
        refine ⟨208093724237685404316004811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138729149491790269544003207 208093724237685404316004811)
        ·
          refine ⟨312140586356528106474007217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208093724237685404316004811 312140586356528106474007217)
          ·
            refine ⟨234105439767396079855505413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312140586356528106474007217 234105439767396079855505413)
            ·
              refine ⟨43894769956386764972907265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234105439767396079855505413 43894769956386764972907265)
              ·
                refine ⟨32921077467290073729680449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43894769956386764972907265 32921077467290073729680449)
                ·
                  refine ⟨24690808100467555297260337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32921077467290073729680449 24690808100467555297260337)
                  ·
                    refine ⟨18518106075350666472945253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24690808100467555297260337 18518106075350666472945253)
                    ·
                      refine ⟨3472144889128249963677235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18518106075350666472945253 3472144889128249963677235)
                      ·
                        rfl

theorem cell23_6761978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_6761978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761978 prefixEnd_6761978 := by exact prefixLift 6761978
  have htrace : WordTrace (prefixWord ++ tailWord_6761978) baseStart_6761978 baseEnd_6761978 := by
    simpa [prefixWord, tailWord_6761978, baseEnd_6761978] using wordTrace_append hprefix tailTrace_6761978
  have hstable : (prefixWord ++ tailWord_6761978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761978).length < 2 ^ (prefixWord ++ tailWord_6761978).sum := by decide
  have hdescent : baseEnd_6761978 < baseStart_6761978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6761995 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 4]
def baseStart_6761995 : Nat := 118140960795 + 6761995 * 2 ^ 59
def prefixEnd_6761995 : Nat := 4983230072969 + 3 ^ 40 * 6761995 * 2
def baseEnd_6761995 : Nat := 3472153618299376397164657

theorem tailTrace_6761995 : CollatzResearch.WordTrace tailWord_6761995 prefixEnd_6761995 3472153618299376397164657 := by
  unfold tailWord_6761995
  simp only [CollatzResearch.WordTrace]
  refine ⟨246630219137454446648263439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164420146091636297765508959 246630219137454446648263439)
  ·
    refine ⟨369945328706181669972395159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246630219137454446648263439 369945328706181669972395159)
    ·
      refine ⟨554917993059272504958592739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369945328706181669972395159 554917993059272504958592739)
      ·
        refine ⟨832376989588908757437889109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554917993059272504958592739 832376989588908757437889109)
        ·
          refine ⟨9754417846745024501225263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 832376989588908757437889109 9754417846745024501225263)
          ·
            refine ⟨14631626770117536751837895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754417846745024501225263 14631626770117536751837895)
            ·
              refine ⟨21947440155176305127756843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14631626770117536751837895 21947440155176305127756843)
              ·
                refine ⟨32921160232764457691635265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21947440155176305127756843 32921160232764457691635265)
                ·
                  refine ⟨24690870174573343268726449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32921160232764457691635265 24690870174573343268726449)
                  ·
                    refine ⟨18518152630930007451544837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24690870174573343268726449 18518152630930007451544837)
                    ·
                      refine ⟨3472153618299376397164657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18518152630930007451544837 3472153618299376397164657)
                      ·
                        rfl

theorem cell23_6761995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 4].length) (baseStart_6761995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6761995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6761995 prefixEnd_6761995 := by exact prefixLift 6761995
  have htrace : WordTrace (prefixWord ++ tailWord_6761995) baseStart_6761995 baseEnd_6761995 := by
    simpa [prefixWord, tailWord_6761995, baseEnd_6761995] using wordTrace_append hprefix tailTrace_6761995
  have hstable : (prefixWord ++ tailWord_6761995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6761995).length < 2 ^ (prefixWord ++ tailWord_6761995).sum := by decide
  have hdescent : baseEnd_6761995 < baseStart_6761995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6761995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762065 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 3, 4]
def baseStart_6762065 : Nat := 118140960795 + 6762065 * 2 ^ 59
def prefixEnd_6762065 : Nat := 4983230072969 + 3 ^ 40 * 6762065 * 2
def baseEnd_6762065 : Nat := 1157396520648397041096445

theorem tailTrace_6762065 : CollatzResearch.WordTrace tailWord_6762065 prefixEnd_6762065 1157396520648397041096445 := by
  unfold tailWord_6762065
  simp only [CollatzResearch.WordTrace]
  refine ⟨246632772247200848603311649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164421848164800565735541099 246632772247200848603311649)
  ·
    refine ⟨184974579185400636452483737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246632772247200848603311649 184974579185400636452483737)
    ·
      refine ⟨138730934389050477339362803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184974579185400636452483737 138730934389050477339362803)
      ·
        refine ⟨208096401583575716009044205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138730934389050477339362803 208096401583575716009044205)
        ·
          refine ⟨78036150593840893503391577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208096401583575716009044205 78036150593840893503391577)
          ·
            refine ⟨58527112945380670127543683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78036150593840893503391577 58527112945380670127543683)
            ·
              refine ⟨87790669418071005191315525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58527112945380670127543683 87790669418071005191315525)
              ·
                refine ⟨16460750515888313473371661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87790669418071005191315525 16460750515888313473371661)
                ·
                  refine ⟨6172781443458117552514373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16460750515888313473371661 6172781443458117552514373)
                  ·
                    refine ⟨1157396520648397041096445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6172781443458117552514373 1157396520648397041096445)
                    ·
                      rfl

theorem cell23_6762065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_6762065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762065 prefixEnd_6762065 := by exact prefixLift 6762065
  have htrace : WordTrace (prefixWord ++ tailWord_6762065) baseStart_6762065 baseEnd_6762065 := by
    simpa [prefixWord, tailWord_6762065, baseEnd_6762065] using wordTrace_append hprefix tailTrace_6762065
  have hstable : (prefixWord ++ tailWord_6762065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762065).length < 2 ^ (prefixWord ++ tailWord_6762065).sum := by decide
  have hdescent : baseEnd_6762065 < baseStart_6762065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762108 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_6762108 : Nat := 118140960795 + 6762108 * 2 ^ 59
def prefixEnd_6762108 : Nat := 4983230072969 + 3 ^ 40 * 6762108 * 2
def baseEnd_6762108 : Nat := 1157403880537778151683879

theorem tailTrace_6762108 : CollatzResearch.WordTrace tailWord_6762108 prefixEnd_6762108 1157403880537778151683879 := by
  unfold tailWord_6762108
  simp only [CollatzResearch.WordTrace]
  refine ⟨123317170293022533473563489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164422893724030044631417985 123317170293022533473563489)
  ·
    refine ⟨92487877719766900105172617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123317170293022533473563489 92487877719766900105172617)
    ·
      refine ⟨69365908289825175078879463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92487877719766900105172617 69365908289825175078879463)
      ·
        refine ⟨104048862434737762618319195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69365908289825175078879463 104048862434737762618319195)
        ·
          refine ⟨156073293652106643927478793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104048862434737762618319195 156073293652106643927478793)
          ·
            refine ⟨117054970239079982945609095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156073293652106643927478793 117054970239079982945609095)
            ·
              refine ⟨175582455358619974418413643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117054970239079982945609095 175582455358619974418413643)
              ·
                refine ⟨263373683037929961627620465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175582455358619974418413643 263373683037929961627620465)
                ·
                  refine ⟨197530262278447471220715349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263373683037929961627620465 197530262278447471220715349)
                  ·
                    refine ⟨1157403880537778151683879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 197530262278447471220715349 1157403880537778151683879)
                    ·
                      rfl

theorem cell23_6762108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_6762108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762108 prefixEnd_6762108 := by exact prefixLift 6762108
  have htrace : WordTrace (prefixWord ++ tailWord_6762108) baseStart_6762108 baseEnd_6762108 := by
    simpa [prefixWord, tailWord_6762108, baseEnd_6762108] using wordTrace_append hprefix tailTrace_6762108
  have hstable : (prefixWord ++ tailWord_6762108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762108).length < 2 ^ (prefixWord ++ tailWord_6762108).sum := by decide
  have hdescent : baseEnd_6762108 < baseStart_6762108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762172 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 1, 6]
def baseStart_6762172 : Nat := 118140960795 + 6762172 * 2 ^ 59
def prefixEnd_6762172 : Nat := 4983230072969 + 3 ^ 40 * 6762172 * 2
def baseEnd_6762172 : Nat := 1157414834791740734883781

theorem tailTrace_6762172 : CollatzResearch.WordTrace tailWord_6762172 prefixEnd_6762172 1157414834791740734883781 := by
  unfold tailWord_6762172
  simp only [CollatzResearch.WordTrace]
  refine ⟨123318337428906602938728385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164424449905208803918304513 123318337428906602938728385)
  ·
    refine ⟨92488753071679952204046289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123318337428906602938728385 92488753071679952204046289)
    ·
      refine ⟨69366564803759964153034717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92488753071679952204046289 69366564803759964153034717)
      ·
        refine ⟨26012461801409986557388019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69366564803759964153034717 26012461801409986557388019)
        ·
          refine ⟨39018692702114979836082029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26012461801409986557388019 39018692702114979836082029)
          ·
            refine ⟨14632009763293117438530761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39018692702114979836082029 14632009763293117438530761)
            ·
              refine ⟨10974007322469838078898071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14632009763293117438530761 10974007322469838078898071)
              ·
                refine ⟨16461010983704757118347107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10974007322469838078898071 16461010983704757118347107)
                ·
                  refine ⟨24691516475557135677520661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16461010983704757118347107 24691516475557135677520661)
                  ·
                    refine ⟨1157414834791740734883781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24691516475557135677520661 1157414834791740734883781)
                    ·
                      rfl

theorem cell23_6762172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_6762172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762172 prefixEnd_6762172 := by exact prefixLift 6762172
  have htrace : WordTrace (prefixWord ++ tailWord_6762172) baseStart_6762172 baseEnd_6762172 := by
    simpa [prefixWord, tailWord_6762172, baseEnd_6762172] using wordTrace_append hprefix tailTrace_6762172
  have hstable : (prefixWord ++ tailWord_6762172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762172).length < 2 ^ (prefixWord ++ tailWord_6762172).sum := by decide
  have hdescent : baseEnd_6762172 < baseStart_6762172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762189 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6762189 : Nat := 118140960795 + 6762189 * 2 ^ 59
def prefixEnd_6762189 : Nat := 4983230072969 + 3 ^ 40 * 6762189 * 2
def baseEnd_6762189 : Nat := 1157417744515449546046255

theorem tailTrace_6762189 : CollatzResearch.WordTrace tailWord_6762189 prefixEnd_6762189 1157417744515449546046255 := by
  unfold tailWord_6762189
  simp only [CollatzResearch.WordTrace]
  refine ⟨246637294898751617780825621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164424863265834411853883747 246637294898751617780825621)
  ·
    refine ⟨11561123198378982083476201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 246637294898751617780825621 11561123198378982083476201)
    ·
      refine ⟨8670842398784236562607151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11561123198378982083476201 8670842398784236562607151)
      ·
        refine ⟨13006263598176354843910727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8670842398784236562607151 13006263598176354843910727)
        ·
          refine ⟨19509395397264532265866091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13006263598176354843910727 19509395397264532265866091)
          ·
            refine ⟨29264093095896798398799137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19509395397264532265866091 29264093095896798398799137)
            ·
              refine ⟨21948069821922598799099353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29264093095896798398799137 21948069821922598799099353)
              ·
                refine ⟨16461052366441949099324515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21948069821922598799099353 16461052366441949099324515)
                ·
                  refine ⟨24691578549662923648986773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16461052366441949099324515 24691578549662923648986773)
                  ·
                    refine ⟨1157417744515449546046255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24691578549662923648986773 1157417744515449546046255)
                    ·
                      rfl

theorem cell23_6762189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6762189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762189 prefixEnd_6762189 := by exact prefixLift 6762189
  have htrace : WordTrace (prefixWord ++ tailWord_6762189) baseStart_6762189 baseEnd_6762189 := by
    simpa [prefixWord, tailWord_6762189, baseEnd_6762189] using wordTrace_append hprefix tailTrace_6762189
  have hstable : (prefixWord ++ tailWord_6762189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762189).length < 2 ^ (prefixWord ++ tailWord_6762189).sum := by decide
  have hdescent : baseEnd_6762189 < baseStart_6762189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762195 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 3]
def baseStart_6762195 : Nat := 118140960795 + 6762195 * 2 ^ 59
def prefixEnd_6762195 : Nat := 4983230072969 + 3 ^ 40 * 6762195 * 2
def baseEnd_6762195 : Nat := 3472256314430275614663737

theorem tailTrace_6762195 : CollatzResearch.WordTrace tailWord_6762195 prefixEnd_6762195 3472256314430275614663737 := by
  unfold tailWord_6762195
  simp only [CollatzResearch.WordTrace]
  refine ⟨246637513736729880805544039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164425009157819920537029359 246637513736729880805544039)
  ·
    refine ⟨369956270605094821208316059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246637513736729880805544039 369956270605094821208316059)
    ·
      refine ⟨554934405907642231812474089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369956270605094821208316059 554934405907642231812474089)
      ·
        refine ⟨416200804430731673859355567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554934405907642231812474089 416200804430731673859355567)
        ·
          refine ⟨624301206646097510789033351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416200804430731673859355567 624301206646097510789033351)
          ·
            refine ⟨936451809969146266183550027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624301206646097510789033351 936451809969146266183550027)
            ·
              refine ⟨1404677714953719399275325041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936451809969146266183550027 1404677714953719399275325041)
              ·
                refine ⟨1053508286215289549456493781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404677714953719399275325041 1053508286215289549456493781)
                ·
                  refine ⟨24691600458170848815386573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1053508286215289549456493781 24691600458170848815386573)
                  ·
                    refine ⟨9259350171814068305769965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24691600458170848815386573 9259350171814068305769965)
                    ·
                      refine ⟨3472256314430275614663737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9259350171814068305769965 3472256314430275614663737)
                      ·
                        rfl

theorem cell23_6762195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_6762195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762195 prefixEnd_6762195 := by exact prefixLift 6762195
  have htrace : WordTrace (prefixWord ++ tailWord_6762195) baseStart_6762195 baseEnd_6762195 := by
    simpa [prefixWord, tailWord_6762195, baseEnd_6762195] using wordTrace_append hprefix tailTrace_6762195
  have hstable : (prefixWord ++ tailWord_6762195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762195).length < 2 ^ (prefixWord ++ tailWord_6762195).sum := by decide
  have hdescent : baseEnd_6762195 < baseStart_6762195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762196 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_6762196 : Nat := 118140960795 + 6762196 * 2 ^ 59
def prefixEnd_6762196 : Nat := 4983230072969 + 3 ^ 40 * 6762196 * 2
def baseEnd_6762196 : Nat := 3472256827910930110751233

theorem tailTrace_6762196 : CollatzResearch.WordTrace tailWord_6762196 prefixEnd_6762196 3472256827910930110751233 := by
  unfold tailWord_6762196
  simp only [CollatzResearch.WordTrace]
  refine ⟨123318775104863128988165221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164425033473150838650886961 123318775104863128988165221)
  ·
    refine ⟨23122270332161836685280979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123318775104863128988165221 23122270332161836685280979)
    ·
      refine ⟨34683405498242755027921469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23122270332161836685280979 34683405498242755027921469)
      ·
        refine ⟨13006277061841033135470551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34683405498242755027921469 13006277061841033135470551)
        ·
          refine ⟨19509415592761549703205827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13006277061841033135470551 19509415592761549703205827)
          ·
            refine ⟨29264123389142324554808741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19509415592761549703205827 29264123389142324554808741)
            ·
              refine ⟨5487023135464185854026639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29264123389142324554808741 5487023135464185854026639)
              ·
                refine ⟨8230534703196278781039959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487023135464185854026639 8230534703196278781039959)
                ·
                  refine ⟨12345802054794418171559939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8230534703196278781039959 12345802054794418171559939)
                  ·
                    refine ⟨18518703082191627257339909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12345802054794418171559939 18518703082191627257339909)
                    ·
                      refine ⟨3472256827910930110751233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18518703082191627257339909 3472256827910930110751233)
                      ·
                        rfl

theorem cell23_6762196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_6762196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762196 prefixEnd_6762196 := by exact prefixLift 6762196
  have htrace : WordTrace (prefixWord ++ tailWord_6762196) baseStart_6762196 baseEnd_6762196 := by
    simpa [prefixWord, tailWord_6762196, baseEnd_6762196] using wordTrace_append hprefix tailTrace_6762196
  have hstable : (prefixWord ++ tailWord_6762196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762196).length < 2 ^ (prefixWord ++ tailWord_6762196).sum := by decide
  have hdescent : baseEnd_6762196 < baseStart_6762196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762239 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 1, 3, 2]
def baseStart_6762239 : Nat := 118140960795 + 6762239 * 2 ^ 59
def prefixEnd_6762239 : Nat := 4983230072969 + 3 ^ 40 * 6762239 * 2
def baseEnd_6762239 : Nat := 3472278907579073442513535

theorem tailTrace_6762239 : CollatzResearch.WordTrace tailWord_6762239 prefixEnd_6762239 3472278907579073442513535 := by
  unfold tailWord_6762239
  simp only [CollatzResearch.WordTrace]
  refine ⟨246639118548570476320145771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164426079032380317546763847 246639118548570476320145771)
  ·
    refine ⟨369958677822855714480218657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246639118548570476320145771 369958677822855714480218657)
    ·
      refine ⟨277469008367141785860163993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369958677822855714480218657 277469008367141785860163993)
      ·
        refine ⟨208101756275356339395122995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277469008367141785860163993 208101756275356339395122995)
        ·
          refine ⟨312152634413034509092684493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208101756275356339395122995 312152634413034509092684493)
          ·
            refine ⟨117057237904887940909756685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312152634413034509092684493 117057237904887940909756685)
            ·
              refine ⟨43896464214332977841158757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117057237904887940909756685 43896464214332977841158757)
              ·
                refine ⟨8230587040187433345217267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43896464214332977841158757 8230587040187433345217267)
                ·
                  refine ⟨12345880560281150017825901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8230587040187433345217267 12345880560281150017825901)
                  ·
                    refine ⟨4629705210105431256684713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12345880560281150017825901 4629705210105431256684713)
                    ·
                      refine ⟨3472278907579073442513535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629705210105431256684713 3472278907579073442513535)
                      ·
                        rfl

theorem cell23_6762239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_6762239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762239 prefixEnd_6762239 := by exact prefixLift 6762239
  have htrace : WordTrace (prefixWord ++ tailWord_6762239) baseStart_6762239 baseEnd_6762239 := by
    simpa [prefixWord, tailWord_6762239, baseEnd_6762239] using wordTrace_append hprefix tailTrace_6762239
  have hstable : (prefixWord ++ tailWord_6762239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762239).length < 2 ^ (prefixWord ++ tailWord_6762239).sum := by decide
  have hdescent : baseEnd_6762239 < baseStart_6762239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762242 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_6762242 : Nat := 118140960795 + 6762242 * 2 ^ 59
def prefixEnd_6762242 : Nat := 4983230072969 + 3 ^ 40 * 6762242 * 2
def baseEnd_6762242 : Nat := 3472280448021036930776021

theorem tailTrace_6762242 : CollatzResearch.WordTrace tailWord_6762242 prefixEnd_6762242 3472280448021036930776021 := by
  unfold tailWord_6762242
  simp only [CollatzResearch.WordTrace]
  refine ⟨61659806991889901958126245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164426151978373071888336653 61659806991889901958126245)
  ·
    refine ⟨11561213810979356617148671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61659806991889901958126245 11561213810979356617148671)
    ·
      refine ⟨17341820716469034925723007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11561213810979356617148671 17341820716469034925723007)
      ·
        refine ⟨26012731074703552388584511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17341820716469034925723007 26012731074703552388584511)
        ·
          refine ⟨39019096612055328582876767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26012731074703552388584511 39019096612055328582876767)
          ·
            refine ⟨58528644918082992874315151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39019096612055328582876767 58528644918082992874315151)
            ·
              refine ⟨87792967377124489311472727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58528644918082992874315151 87792967377124489311472727)
              ·
                refine ⟨131689451065686733967209091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87792967377124489311472727 131689451065686733967209091)
                ·
                  refine ⟨197534176598530100950813637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131689451065686733967209091 197534176598530100950813637)
                  ·
                    refine ⟨37037658112224393928277557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197534176598530100950813637 37037658112224393928277557)
                    ·
                      refine ⟨3472280448021036930776021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37037658112224393928277557 3472280448021036930776021)
                      ·
                        rfl

theorem cell23_6762242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_6762242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762242 prefixEnd_6762242 := by exact prefixLift 6762242
  have htrace : WordTrace (prefixWord ++ tailWord_6762242) baseStart_6762242 baseEnd_6762242 := by
    simpa [prefixWord, tailWord_6762242, baseEnd_6762242] using wordTrace_append hprefix tailTrace_6762242
  have hstable : (prefixWord ++ tailWord_6762242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762242).length < 2 ^ (prefixWord ++ tailWord_6762242).sum := by decide
  have hdescent : baseEnd_6762242 < baseStart_6762242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762247 : List Nat := [1, 1, 4, 4, 3, 1, 1, 3, 1, 2, 2]
def baseStart_6762247 : Nat := 118140960795 + 6762247 * 2 ^ 59
def prefixEnd_6762247 : Nat := 4983230072969 + 3 ^ 40 * 6762247 * 2
def baseEnd_6762247 : Nat := 3472283015424309411213499

theorem tailTrace_6762247 : CollatzResearch.WordTrace tailWord_6762247 prefixEnd_6762247 3472283015424309411213499 := by
  unfold tailWord_6762247
  simp only [CollatzResearch.WordTrace]
  refine ⟨246639410332541493686436995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164426273555027662457624663 246639410332541493686436995)
  ·
    refine ⟨369959115498812240529655493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246639410332541493686436995 369959115498812240529655493)
    ·
      refine ⟨69367334156027295099310405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369959115498812240529655493 69367334156027295099310405)
      ·
        refine ⟨13006375154255117831120701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69367334156027295099310405 13006375154255117831120701)
        ·
          refine ⟨4877390682845669186670263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13006375154255117831120701 4877390682845669186670263)
          ·
            refine ⟨7316086024268503780005395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4877390682845669186670263 7316086024268503780005395)
            ·
              refine ⟨10974129036402755670008093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7316086024268503780005395 10974129036402755670008093)
              ·
                refine ⟨4115298388651033376253035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10974129036402755670008093 4115298388651033376253035)
                ·
                  refine ⟨6172947582976550064379553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115298388651033376253035 6172947582976550064379553)
                  ·
                    refine ⟨4629710687232412548284665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6172947582976550064379553 4629710687232412548284665)
                    ·
                      refine ⟨3472283015424309411213499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629710687232412548284665 3472283015424309411213499)
                      ·
                        rfl

theorem cell23_6762247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_6762247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762247 prefixEnd_6762247 := by exact prefixLift 6762247
  have htrace : WordTrace (prefixWord ++ tailWord_6762247) baseStart_6762247 baseEnd_6762247 := by
    simpa [prefixWord, tailWord_6762247, baseEnd_6762247] using wordTrace_append hprefix tailTrace_6762247
  have hstable : (prefixWord ++ tailWord_6762247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762247).length < 2 ^ (prefixWord ++ tailWord_6762247).sum := by decide
  have hdescent : baseEnd_6762247 < baseStart_6762247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762253 : List Nat := [1, 7, 2, 1, 1, 2, 9]
def baseStart_6762253 : Nat := 118140960795 + 6762253 * 2 ^ 59
def prefixEnd_6762253 : Nat := 4983230072969 + 3 ^ 40 * 6762253 * 2
def baseEnd_6762253 : Nat := 42867729584052301083191

theorem tailTrace_6762253 : CollatzResearch.WordTrace tailWord_6762253 prefixEnd_6762253 42867729584052301083191 := by
  unfold tailWord_6762253
  simp only [CollatzResearch.WordTrace]
  refine ⟨246639629170519756711155413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164426419447013171140770275 246639629170519756711155413)
  ·
    refine ⟨5780616308684056797917705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 246639629170519756711155413 5780616308684056797917705)
    ·
      refine ⟨4335462231513042598438279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5780616308684056797917705 4335462231513042598438279)
      ·
        refine ⟨6503193347269563897657419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335462231513042598438279 6503193347269563897657419)
        ·
          refine ⟨9754790020904345846486129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6503193347269563897657419 9754790020904345846486129)
          ·
            refine ⟨7316092515678259384864597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9754790020904345846486129 7316092515678259384864597)
            ·
              refine ⟨42867729584052301083191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7316092515678259384864597 42867729584052301083191)
              ·
                rfl

theorem cell23_6762253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 9].length) (baseStart_6762253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762253 prefixEnd_6762253 := by exact prefixLift 6762253
  have htrace : WordTrace (prefixWord ++ tailWord_6762253) baseStart_6762253 baseEnd_6762253 := by
    simpa [prefixWord, tailWord_6762253, baseEnd_6762253] using wordTrace_append hprefix tailTrace_6762253
  have hstable : (prefixWord ++ tailWord_6762253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762253).length < 2 ^ (prefixWord ++ tailWord_6762253).sum := by decide
  have hdescent : baseEnd_6762253 < baseStart_6762253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762272 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 3]
def baseStart_6762272 : Nat := 118140960795 + 6762272 * 2 ^ 59
def prefixEnd_6762272 : Nat := 4983230072969 + 3 ^ 40 * 6762272 * 2
def baseEnd_6762272 : Nat := 3472295852440671813400883

theorem tailTrace_6762272 : CollatzResearch.WordTrace tailWord_6762272 prefixEnd_6762272 3472295852440671813400883 := by
  unfold tailWord_6762272
  simp only [CollatzResearch.WordTrace]
  refine ⟨123320161078725461478048535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164426881438300615304064713 123320161078725461478048535)
  ·
    refine ⟨184980241618088192217072803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123320161078725461478048535 184980241618088192217072803)
    ·
      refine ⟨277470362427132288325609205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184980241618088192217072803 277470362427132288325609205)
      ·
        refine ⟨26012846477543652030525863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277470362427132288325609205 26012846477543652030525863)
        ·
          refine ⟨39019269716315478045788795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26012846477543652030525863 39019269716315478045788795)
          ·
            refine ⟨58528904574473217068683193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39019269716315478045788795 58528904574473217068683193)
            ·
              refine ⟨43896678430854912801512395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58528904574473217068683193 43896678430854912801512395)
              ·
                refine ⟨65845017646282369202268593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43896678430854912801512395 65845017646282369202268593)
                ·
                  refine ⟨49383763234711776901701445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65845017646282369202268593 49383763234711776901701445)
                  ·
                    refine ⟨9259455606508458169069021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49383763234711776901701445 9259455606508458169069021)
                    ·
                      refine ⟨3472295852440671813400883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9259455606508458169069021 3472295852440671813400883)
                      ·
                        rfl

theorem cell23_6762272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_6762272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762272 prefixEnd_6762272 := by exact prefixLift 6762272
  have htrace : WordTrace (prefixWord ++ tailWord_6762272) baseStart_6762272 baseEnd_6762272 := by
    simpa [prefixWord, tailWord_6762272, baseEnd_6762272] using wordTrace_append hprefix tailTrace_6762272
  have hstable : (prefixWord ++ tailWord_6762272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762272).length < 2 ^ (prefixWord ++ tailWord_6762272).sum := by decide
  have hdescent : baseEnd_6762272 < baseStart_6762272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762372 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_6762372 : Nat := 118140960795 + 6762372 * 2 ^ 59
def prefixEnd_6762372 : Nat := 4983230072969 + 3 ^ 40 * 6762372 * 2
def baseEnd_6762372 : Nat := 3472347200506121422150423

theorem tailTrace_6762372 : CollatzResearch.WordTrace tailWord_6762372 prefixEnd_6762372 3472347200506121422150423 := by
  unfold tailWord_6762372
  simp only [CollatzResearch.WordTrace]
  refine ⟨123321984728544320017368685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164429312971392426689824913 123321984728544320017368685)
  ·
    refine ⟨46245744273204120006513257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123321984728544320017368685 46245744273204120006513257)
    ·
      refine ⟨34684308204903090004884943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46245744273204120006513257 34684308204903090004884943)
      ·
        refine ⟨52026462307354635007327415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34684308204903090004884943 52026462307354635007327415)
        ·
          refine ⟨78039693461031952510991123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52026462307354635007327415 78039693461031952510991123)
          ·
            refine ⟨117059540191547928766486685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78039693461031952510991123 117059540191547928766486685)
            ·
              refine ⟨43897327571830473287432507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117059540191547928766486685 43897327571830473287432507)
              ·
                refine ⟨65845991357745709931148761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43897327571830473287432507 65845991357745709931148761)
                ·
                  refine ⟨49384493518309282448361571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65845991357745709931148761 49384493518309282448361571)
                  ·
                    refine ⟨74076740277463923672542357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49384493518309282448361571 74076740277463923672542357)
                    ·
                      refine ⟨3472347200506121422150423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74076740277463923672542357 3472347200506121422150423)
                      ·
                        rfl

theorem cell23_6762372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_6762372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762372 prefixEnd_6762372 := by exact prefixLift 6762372
  have htrace : WordTrace (prefixWord ++ tailWord_6762372) baseStart_6762372 baseEnd_6762372 := by
    simpa [prefixWord, tailWord_6762372, baseEnd_6762372] using wordTrace_append hprefix tailTrace_6762372
  have hstable : (prefixWord ++ tailWord_6762372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762372).length < 2 ^ (prefixWord ++ tailWord_6762372).sum := by decide
  have hdescent : baseEnd_6762372 < baseStart_6762372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762386 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_6762386 : Nat := 118140960795 + 6762386 * 2 ^ 59
def prefixEnd_6762386 : Nat := 4983230072969 + 3 ^ 40 * 6762386 * 2
def baseEnd_6762386 : Nat := 1157451463078428122458453

theorem tailTrace_6762386 : CollatzResearch.WordTrace tailWord_6762386 prefixEnd_6762386 1157451463078428122458453 := by
  unfold tailWord_6762386
  simp only [CollatzResearch.WordTrace]
  refine ⟨61661120019759480106436753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164429653386025280283831341 61661120019759480106436753)
  ·
    refine ⟨46245840014819610079827565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61661120019759480106436753 46245840014819610079827565)
    ·
      refine ⟨17342190005557353779935337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46245840014819610079827565 17342190005557353779935337)
      ·
        refine ⟨13006642504168015334951503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17342190005557353779935337 13006642504168015334951503)
        ·
          refine ⟨19509963756252023002427255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13006642504168015334951503 19509963756252023002427255)
          ·
            refine ⟨29264945634378034503640883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19509963756252023002427255 29264945634378034503640883)
            ·
              refine ⟨43897418451567051755461325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29264945634378034503640883 43897418451567051755461325)
              ·
                refine ⟨16461531919337644408297997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43897418451567051755461325 16461531919337644408297997)
                ·
                  refine ⟨6173074469751616653111749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16461531919337644408297997 6173074469751616653111749)
                  ·
                    refine ⟨1157451463078428122458453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173074469751616653111749 1157451463078428122458453)
                    ·
                      rfl

theorem cell23_6762386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_6762386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762386 prefixEnd_6762386 := by exact prefixLift 6762386
  have htrace : WordTrace (prefixWord ++ tailWord_6762386) baseStart_6762386 baseEnd_6762386 := by
    simpa [prefixWord, tailWord_6762386, baseEnd_6762386] using wordTrace_append hprefix tailTrace_6762386
  have hstable : (prefixWord ++ tailWord_6762386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762386).length < 2 ^ (prefixWord ++ tailWord_6762386).sum := by decide
  have hdescent : baseEnd_6762386 < baseStart_6762386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762409 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 3]
def baseStart_6762409 : Nat := 118140960795 + 6762409 * 2 ^ 59
def prefixEnd_6762409 : Nat := 4983230072969 + 3 ^ 40 * 6762409 * 2
def baseEnd_6762409 : Nat := 3472366199290337777387753

theorem tailTrace_6762409 : CollatzResearch.WordTrace tailWord_6762409 prefixEnd_6762409 3472366199290337777387753 := by
  unfold tailWord_6762409
  simp only [CollatzResearch.WordTrace]
  refine ⟨246645318957954595353834281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164430212638636396902556187 246645318957954595353834281)
  ·
    refine ⟨184983989218465946515375711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246645318957954595353834281 184983989218465946515375711)
    ·
      refine ⟨277475983827698919773063567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184983989218465946515375711 277475983827698919773063567)
      ·
        refine ⟨416213975741548379659595351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277475983827698919773063567 416213975741548379659595351)
        ·
          refine ⟨624320963612322569489393027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416213975741548379659595351 624320963612322569489393027)
          ·
            refine ⟨936481445418483854234089541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624320963612322569489393027 936481445418483854234089541)
            ·
              refine ⟨175590271015965722668891789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 936481445418483854234089541 175590271015965722668891789)
              ·
                refine ⟨65846351630987146000834421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175590271015965722668891789 65846351630987146000834421)
                ·
                  refine ⟨6173095465405044937578227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65846351630987146000834421 6173095465405044937578227)
                  ·
                    refine ⟨9259643198107567406367341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6173095465405044937578227 9259643198107567406367341)
                    ·
                      refine ⟨3472366199290337777387753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9259643198107567406367341 3472366199290337777387753)
                      ·
                        rfl

theorem cell23_6762409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 1, 3].length) (baseStart_6762409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762409 prefixEnd_6762409 := by exact prefixLift 6762409
  have htrace : WordTrace (prefixWord ++ tailWord_6762409) baseStart_6762409 baseEnd_6762409 := by
    simpa [prefixWord, tailWord_6762409, baseEnd_6762409] using wordTrace_append hprefix tailTrace_6762409
  have hstable : (prefixWord ++ tailWord_6762409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762409).length < 2 ^ (prefixWord ++ tailWord_6762409).sum := by decide
  have hdescent : baseEnd_6762409 < baseStart_6762409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762419 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 1, 5, 2]
def baseStart_6762419 : Nat := 118140960795 + 6762419 * 2 ^ 59
def prefixEnd_6762419 : Nat := 4983230072969 + 3 ^ 40 * 6762419 * 2
def baseEnd_6762419 : Nat := 3472371334096882738262707

theorem tailTrace_6762419 : CollatzResearch.WordTrace tailWord_6762419 prefixEnd_6762419 3472371334096882738262707 := by
  unfold tailWord_6762419
  simp only [CollatzResearch.WordTrace]
  refine ⟨246645683687918367061698311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164430455791945578041132207 246645683687918367061698311)
  ·
    refine ⟨369968525531877550592547467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246645683687918367061698311 369968525531877550592547467)
    ·
      refine ⟨554952788297816325888821201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369968525531877550592547467 554952788297816325888821201)
      ·
        refine ⟨416214591223362244416615901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554952788297816325888821201 416214591223362244416615901)
        ·
          refine ⟨156080471708760841656230963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416214591223362244416615901 156080471708760841656230963)
          ·
            refine ⟨234120707563141262484346445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156080471708760841656230963 234120707563141262484346445)
            ·
              refine ⟨87795265336177973431629917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234120707563141262484346445 87795265336177973431629917)
              ·
                refine ⟨32923224501066740036861219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87795265336177973431629917 32923224501066740036861219)
                ·
                  refine ⟨49384836751600110055291829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32923224501066740036861219 49384836751600110055291829)
                  ·
                    refine ⟨4629828445462510317683609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49384836751600110055291829 4629828445462510317683609)
                    ·
                      refine ⟨3472371334096882738262707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629828445462510317683609 3472371334096882738262707)
                      ·
                        rfl

theorem cell23_6762419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 5, 2].length) (baseStart_6762419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762419 prefixEnd_6762419 := by exact prefixLift 6762419
  have htrace : WordTrace (prefixWord ++ tailWord_6762419) baseStart_6762419 baseEnd_6762419 := by
    simpa [prefixWord, tailWord_6762419, baseEnd_6762419] using wordTrace_append hprefix tailTrace_6762419
  have hstable : (prefixWord ++ tailWord_6762419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762419).length < 2 ^ (prefixWord ++ tailWord_6762419).sum := by decide
  have hdescent : baseEnd_6762419 < baseStart_6762419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762449 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 2, 6, 2]
def baseStart_6762449 : Nat := 118140960795 + 6762449 * 2 ^ 59
def prefixEnd_6762449 : Nat := 4983230072969 + 3 ^ 40 * 6762449 * 2
def baseEnd_6762449 : Nat := 3472386738516517620887569

theorem tailTrace_6762449 : CollatzResearch.WordTrace tailWord_6762449 prefixEnd_6762449 3472386738516517620887569 := by
  unfold tailWord_6762449
  simp only [CollatzResearch.WordTrace]
  refine ⟨246646777877809682185290401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164431185251873121456860267 246646777877809682185290401)
  ·
    refine ⟨184985083408357261638967801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246646777877809682185290401 184985083408357261638967801)
    ·
      refine ⟨138738812556267946229225851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184985083408357261638967801 138738812556267946229225851)
      ·
        refine ⟨208108218834401919343838777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138738812556267946229225851 208108218834401919343838777)
        ·
          refine ⟨156081164125801439507879083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208108218834401919343838777 156081164125801439507879083)
          ·
            refine ⟨234121746188702159261818625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156081164125801439507879083 234121746188702159261818625)
            ·
              refine ⟨175591309641526619446363969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234121746188702159261818625 175591309641526619446363969)
              ·
                refine ⟨131693482231144964584772977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175591309641526619446363969 131693482231144964584772977)
                ·
                  refine ⟨98770111673358723438579733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131693482231144964584772977 98770111673358723438579733)
                  ·
                    refine ⟨4629848984688690161183425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98770111673358723438579733 4629848984688690161183425)
                    ·
                      refine ⟨3472386738516517620887569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629848984688690161183425 3472386738516517620887569)
                      ·
                        rfl

theorem cell23_6762449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_6762449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762449 prefixEnd_6762449 := by exact prefixLift 6762449
  have htrace : WordTrace (prefixWord ++ tailWord_6762449) baseStart_6762449 baseEnd_6762449 := by
    simpa [prefixWord, tailWord_6762449, baseEnd_6762449] using wordTrace_append hprefix tailTrace_6762449
  have hstable : (prefixWord ++ tailWord_6762449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762449).length < 2 ^ (prefixWord ++ tailWord_6762449).sum := by decide
  have hdescent : baseEnd_6762449 < baseStart_6762449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762450 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 6]
def baseStart_6762450 : Nat := 118140960795 + 6762450 * 2 ^ 59
def prefixEnd_6762450 : Nat := 4983230072969 + 3 ^ 40 * 6762450 * 2
def baseEnd_6762450 : Nat := 385820805777463568552785

theorem tailTrace_6762450 : CollatzResearch.WordTrace tailWord_6762450 prefixEnd_6762450 385820805777463568552785 := by
  unfold tailWord_6762450
  simp only [CollatzResearch.WordTrace]
  refine ⟨61661703587701514839019201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164431209567204039570717869 61661703587701514839019201)
  ·
    refine ⟨46246277690776136129264401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61661703587701514839019201 46246277690776136129264401)
    ·
      refine ⟨34684708268082102096948301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46246277690776136129264401 34684708268082102096948301)
      ·
        refine ⟨13006765600530788286355613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34684708268082102096948301 13006765600530788286355613)
        ·
          refine ⟨4877537100199045607383355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13006765600530788286355613 4877537100199045607383355)
          ·
            refine ⟨7316305650298568411075033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4877537100199045607383355 7316305650298568411075033)
            ·
              refine ⟨5487229237723926308306275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7316305650298568411075033 5487229237723926308306275)
              ·
                refine ⟨8230843856585889462459413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487229237723926308306275 8230843856585889462459413)
                ·
                  refine ⟨385820805777463568552785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8230843856585889462459413 385820805777463568552785)
                  ·
                    rfl

theorem cell23_6762450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_6762450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762450 prefixEnd_6762450 := by exact prefixLift 6762450
  have htrace : WordTrace (prefixWord ++ tailWord_6762450) baseStart_6762450 baseEnd_6762450 := by
    simpa [prefixWord, tailWord_6762450, baseEnd_6762450] using wordTrace_append hprefix tailTrace_6762450
  have hstable : (prefixWord ++ tailWord_6762450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762450).length < 2 ^ (prefixWord ++ tailWord_6762450).sum := by decide
  have hdescent : baseEnd_6762450 < baseStart_6762450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762479 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_6762479 : Nat := 118140960795 + 6762479 * 2 ^ 59
def prefixEnd_6762479 : Nat := 4983230072969 + 3 ^ 40 * 6762479 * 2
def baseEnd_6762479 : Nat := 3472402142936152503512431

theorem tailTrace_6762479 : CollatzResearch.WordTrace tailWord_6762479 prefixEnd_6762479 3472402142936152503512431 := by
  unfold tailWord_6762479
  simp only [CollatzResearch.WordTrace]
  refine ⟨246647872067700997308882491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164431914711800664872588327 246647872067700997308882491)
  ·
    refine ⟨369971808101551495963323737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246647872067700997308882491 369971808101551495963323737)
    ·
      refine ⟨277478856076163621972492803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369971808101551495963323737 277478856076163621972492803)
      ·
        refine ⟨416218284114245432958739205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277478856076163621972492803 416218284114245432958739205)
        ·
          refine ⟨78040928271421018679763601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 416218284114245432958739205 78040928271421018679763601)
          ·
            refine ⟨58530696203565764009822701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78040928271421018679763601 58530696203565764009822701)
            ·
              refine ⟨21949011076337161503683513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58530696203565764009822701 21949011076337161503683513)
              ·
                refine ⟨16461758307252871127762635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21949011076337161503683513 16461758307252871127762635)
                ·
                  refine ⟨24692637460879306691643953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16461758307252871127762635 24692637460879306691643953)
                  ·
                    refine ⟨18519478095659480018732965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24692637460879306691643953 18519478095659480018732965)
                    ·
                      refine ⟨3472402142936152503512431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18519478095659480018732965 3472402142936152503512431)
                      ·
                        rfl

theorem cell23_6762479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_6762479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762479 prefixEnd_6762479 := by exact prefixLift 6762479
  have htrace : WordTrace (prefixWord ++ tailWord_6762479) baseStart_6762479 baseEnd_6762479 := by
    simpa [prefixWord, tailWord_6762479, baseEnd_6762479] using wordTrace_append hprefix tailTrace_6762479
  have hstable : (prefixWord ++ tailWord_6762479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762479).length < 2 ^ (prefixWord ++ tailWord_6762479).sum := by decide
  have hdescent : baseEnd_6762479 < baseStart_6762479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762494 : List Nat := [4, 2, 2, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_6762494 : Nat := 118140960795 + 6762494 * 2 ^ 59
def prefixEnd_6762494 : Nat := 4983230072969 + 3 ^ 40 * 6762494 * 2
def baseEnd_6762494 : Nat := 3472409845145969944824863

theorem tailTrace_6762494 : CollatzResearch.WordTrace tailWord_6762494 prefixEnd_6762494 3472409845145969944824863 := by
  unfold tailWord_6762494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30831052395330831858834817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164432279441764436580452357 30831052395330831858834817)
  ·
    refine ⟨23123289296498123894126113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30831052395330831858834817 23123289296498123894126113)
    ·
      refine ⟨17342466972373592920594585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23123289296498123894126113 17342466972373592920594585)
      ·
        refine ⟨13006850229280194690445939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17342466972373592920594585 13006850229280194690445939)
        ·
          refine ⟨19510275343920292035668909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13006850229280194690445939 19510275343920292035668909)
          ·
            refine ⟨7316353253970109513375841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19510275343920292035668909 7316353253970109513375841)
            ·
              refine ⟨5487264940477582135031881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7316353253970109513375841 5487264940477582135031881)
              ·
                refine ⟨4115448705358186601273911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5487264940477582135031881 4115448705358186601273911)
                ·
                  refine ⟨6173173058037279901910867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115448705358186601273911 6173173058037279901910867)
                  ·
                    refine ⟨9259759587055919852866301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6173173058037279901910867 9259759587055919852866301)
                    ·
                      refine ⟨3472409845145969944824863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9259759587055919852866301 3472409845145969944824863)
                      ·
                        rfl

theorem cell23_6762494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_6762494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762494 prefixEnd_6762494 := by exact prefixLift 6762494
  have htrace : WordTrace (prefixWord ++ tailWord_6762494) baseStart_6762494 baseEnd_6762494 := by
    simpa [prefixWord, tailWord_6762494, baseEnd_6762494] using wordTrace_append hprefix tailTrace_6762494
  have hstable : (prefixWord ++ tailWord_6762494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762494).length < 2 ^ (prefixWord ++ tailWord_6762494).sum := by decide
  have hdescent : baseEnd_6762494 < baseStart_6762494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762506 : List Nat := [3, 1, 2, 2, 4, 2, 1, 8]
def baseStart_6762506 : Nat := 118140960795 + 6762506 * 2 ^ 59
def prefixEnd_6762506 : Nat := 4983230072969 + 3 ^ 40 * 6762506 * 2
def baseEnd_6762506 : Nat := 128608000256067551773141

theorem tailTrace_6762506 : CollatzResearch.WordTrace tailWord_6762506 prefixEnd_6762506 128608000256067551773141 := by
  unfold tailWord_6762506
  simp only [CollatzResearch.WordTrace]
  refine ⟨61662214209650795230028843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164432571225735453946743581 61662214209650795230028843)
  ·
    refine ⟨92493321314476192845043265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61662214209650795230028843 92493321314476192845043265)
    ·
      refine ⟨69369990985857144633782449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92493321314476192845043265 69369990985857144633782449)
      ·
        refine ⟨52027493239392858475336837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69369990985857144633782449 52027493239392858475336837)
        ·
          refine ⟨9755154982386160964125657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52027493239392858475336837 9755154982386160964125657)
          ·
            refine ⟨7316366236789620723094243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9755154982386160964125657 7316366236789620723094243)
            ·
              refine ⟨10974549355184431084641365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7316366236789620723094243 10974549355184431084641365)
              ·
                refine ⟨128608000256067551773141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10974549355184431084641365 128608000256067551773141)
                ·
                  rfl

theorem cell23_6762506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 8].length) (baseStart_6762506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762506 prefixEnd_6762506 := by exact prefixLift 6762506
  have htrace : WordTrace (prefixWord ++ tailWord_6762506) baseStart_6762506 baseEnd_6762506 := by
    simpa [prefixWord, tailWord_6762506, baseEnd_6762506] using wordTrace_append hprefix tailTrace_6762506
  have hstable : (prefixWord ++ tailWord_6762506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762506).length < 2 ^ (prefixWord ++ tailWord_6762506).sum := by decide
  have hdescent : baseEnd_6762506 < baseStart_6762506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762549 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_6762549 : Nat := 118140960795 + 6762549 * 2 ^ 59
def prefixEnd_6762549 : Nat := 4983230072969 + 3 ^ 40 * 6762549 * 2
def baseEnd_6762549 : Nat := 1157479362193989076545703

theorem tailTrace_6762549 : CollatzResearch.WordTrace tailWord_6762549 prefixEnd_6762549 1157479362193989076545703 := by
  unfold tailWord_6762549
  simp only [CollatzResearch.WordTrace]
  refine ⟨246650425177447399263930701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164433616784964932842620467 246650425177447399263930701)
  ·
    refine ⟨92493909441542774723974013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246650425177447399263930701 92493909441542774723974013)
    ·
      refine ⟨34685216040578540521490255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92493909441542774723974013 34685216040578540521490255)
      ·
        refine ⟨52027824060867810782235383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34685216040578540521490255 52027824060867810782235383)
        ·
          refine ⟨78041736091301716173353075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52027824060867810782235383 78041736091301716173353075)
          ·
            refine ⟨117062604136952574260029613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78041736091301716173353075 117062604136952574260029613)
            ·
              refine ⟨43898476551357215347511105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117062604136952574260029613 43898476551357215347511105)
              ·
                refine ⟨32923857413517911510633329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43898476551357215347511105 32923857413517911510633329)
                ·
                  refine ⟨24692893060138433632974997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32923857413517911510633329 24692893060138433632974997)
                  ·
                    refine ⟨1157479362193989076545703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24692893060138433632974997 1157479362193989076545703)
                    ·
                      rfl

theorem cell23_6762549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_6762549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762549 prefixEnd_6762549 := by exact prefixLift 6762549
  have htrace : WordTrace (prefixWord ++ tailWord_6762549) baseStart_6762549 baseEnd_6762549 := by
    simpa [prefixWord, tailWord_6762549, baseEnd_6762549] using wordTrace_append hprefix tailTrace_6762549
  have hstable : (prefixWord ++ tailWord_6762549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762549).length < 2 ^ (prefixWord ++ tailWord_6762549).sum := by decide
  have hdescent : baseEnd_6762549 < baseStart_6762549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762559 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 3]
def baseStart_6762559 : Nat := 118140960795 + 6762559 * 2 ^ 59
def prefixEnd_6762559 : Nat := 4983230072969 + 3 ^ 40 * 6762559 * 2
def baseEnd_6762559 : Nat := 3472443221388512190512063

theorem tailTrace_6762559 : CollatzResearch.WordTrace tailWord_6762559 prefixEnd_6762559 3472443221388512190512063 := by
  unfold tailWord_6762559
  simp only [CollatzResearch.WordTrace]
  refine ⟨246650789907411170971794731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164433859938274113981196487 246650789907411170971794731)
  ·
    refine ⟨369976184861116756457692097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246650789907411170971794731 369976184861116756457692097)
    ·
      refine ⟨277482138645837567343269073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369976184861116756457692097 277482138645837567343269073)
      ·
        refine ⟨208111603984378175507451805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277482138645837567343269073 208111603984378175507451805)
        ·
          refine ⟨78041851494141815815294427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208111603984378175507451805 78041851494141815815294427)
          ·
            refine ⟨117062777241212723722941641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78041851494141815815294427 117062777241212723722941641)
            ·
              refine ⟨87797082930909542792206231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117062777241212723722941641 87797082930909542792206231)
              ·
                refine ⟨131695624396364314188309347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87797082930909542792206231 131695624396364314188309347)
                ·
                  refine ⟨197543436594546471282464021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131695624396364314188309347 197543436594546471282464021)
                  ·
                    refine ⟨9259848590369365841365501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 197543436594546471282464021 9259848590369365841365501)
                    ·
                      refine ⟨3472443221388512190512063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9259848590369365841365501 3472443221388512190512063)
                      ·
                        rfl

theorem cell23_6762559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_6762559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762559 prefixEnd_6762559 := by exact prefixLift 6762559
  have htrace : WordTrace (prefixWord ++ tailWord_6762559) baseStart_6762559 baseEnd_6762559 := by
    simpa [prefixWord, tailWord_6762559, baseEnd_6762559] using wordTrace_append hprefix tailTrace_6762559
  have hstable : (prefixWord ++ tailWord_6762559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762559).length < 2 ^ (prefixWord ++ tailWord_6762559).sum := by decide
  have hdescent : baseEnd_6762559 < baseStart_6762559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762569 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_6762569 : Nat := 118140960795 + 6762569 * 2 ^ 59
def prefixEnd_6762569 : Nat := 4983230072969 + 3 ^ 40 * 6762569 * 2
def baseEnd_6762569 : Nat := 3472448356195057151387017

theorem tailTrace_6762569 : CollatzResearch.WordTrace tailWord_6762569 prefixEnd_6762569 3472448356195057151387017 := by
  unfold tailWord_6762569
  simp only [CollatzResearch.WordTrace]
  refine ⟨246651154637374942679658761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164434103091583295119772507 246651154637374942679658761)
  ·
    refine ⟨184988365978031207009744071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246651154637374942679658761 184988365978031207009744071)
    ·
      refine ⟨277482548967046810514616107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184988365978031207009744071 277482548967046810514616107)
      ·
        refine ⟨416223823450570215771924161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277482548967046810514616107 416223823450570215771924161)
        ·
          refine ⟨312167867587927661828943121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416223823450570215771924161 312167867587927661828943121)
          ·
            refine ⟨234125900690945746371707341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312167867587927661828943121 234125900690945746371707341)
            ·
              refine ⟨87797212759104654889390253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234125900690945746371707341 87797212759104654889390253)
              ·
                refine ⟨32923954784664245583521345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87797212759104654889390253 32923954784664245583521345)
                ·
                  refine ⟨24692966088498184187641009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32923954784664245583521345 24692966088498184187641009)
                  ·
                    refine ⟨18519724566373638140730757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24692966088498184187641009 18519724566373638140730757)
                    ·
                      refine ⟨3472448356195057151387017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18519724566373638140730757 3472448356195057151387017)
                      ·
                        rfl

theorem cell23_6762569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_6762569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762569 prefixEnd_6762569 := by exact prefixLift 6762569
  have htrace : WordTrace (prefixWord ++ tailWord_6762569) baseStart_6762569 baseEnd_6762569 := by
    simpa [prefixWord, tailWord_6762569, baseEnd_6762569] using wordTrace_append hprefix tailTrace_6762569
  have hstable : (prefixWord ++ tailWord_6762569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762569).length < 2 ^ (prefixWord ++ tailWord_6762569).sum := by decide
  have hdescent : baseEnd_6762569 < baseStart_6762569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762616 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 2, 5, 2]
def baseStart_6762616 : Nat := 118140960795 + 6762616 * 2 ^ 59
def prefixEnd_6762616 : Nat := 4983230072969 + 3 ^ 40 * 6762616 * 2
def baseEnd_6762616 : Nat := 3472472489785818467499301

theorem tailTrace_6762616 : CollatzResearch.WordTrace tailWord_6762616 prefixEnd_6762616 3472472489785818467499301 := by
  unfold tailWord_6762616
  simp only [CollatzResearch.WordTrace]
  refine ⟨123326434434102334853309851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164435245912136446471079801 123326434434102334853309851)
  ·
    refine ⟨184989651651153502279964777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123326434434102334853309851 184989651651153502279964777)
    ·
      refine ⟨138742238738365126709973583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184989651651153502279964777 138742238738365126709973583)
      ·
        refine ⟨208113358107547690064960375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138742238738365126709973583 208113358107547690064960375)
        ·
          refine ⟨312170037161321535097440563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208113358107547690064960375 312170037161321535097440563)
          ·
            refine ⟨468255055741982302646160845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312170037161321535097440563 468255055741982302646160845)
            ·
              refine ⟨175595645903243363492310317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468255055741982302646160845 175595645903243363492310317)
              ·
                refine ⟨65848367213716261309616369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175595645903243363492310317 65848367213716261309616369)
                ·
                  refine ⟨49386275410287195982212277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65848367213716261309616369 49386275410287195982212277)
                  ·
                    refine ⟨4629963319714424623332401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49386275410287195982212277 4629963319714424623332401)
                    ·
                      refine ⟨3472472489785818467499301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4629963319714424623332401 3472472489785818467499301)
                      ·
                        rfl

theorem cell23_6762616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_6762616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762616 prefixEnd_6762616 := by exact prefixLift 6762616
  have htrace : WordTrace (prefixWord ++ tailWord_6762616) baseStart_6762616 baseEnd_6762616 := by
    simpa [prefixWord, tailWord_6762616, baseEnd_6762616] using wordTrace_append hprefix tailTrace_6762616
  have hstable : (prefixWord ++ tailWord_6762616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762616).length < 2 ^ (prefixWord ++ tailWord_6762616).sum := by decide
  have hdescent : baseEnd_6762616 < baseStart_6762616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762700 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6762700 : Nat := 118140960795 + 6762700 * 2 ^ 59
def prefixEnd_6762700 : Nat := 4983230072969 + 3 ^ 40 * 6762700 * 2
def baseEnd_6762700 : Nat := 3472515622160796138848915

theorem tailTrace_6762700 : CollatzResearch.WordTrace tailWord_6762700 prefixEnd_6762700 3472515622160796138848915 := by
  unfold tailWord_6762700
  simp only [CollatzResearch.WordTrace]
  refine ⟨123327966299950176026338777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164437288399933568035118369 123327966299950176026338777)
  ·
    refine ⟨92495974724962632019754083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123327966299950176026338777 92495974724962632019754083)
    ·
      refine ⟨138743962087443948029631125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92495974724962632019754083 138743962087443948029631125)
      ·
        refine ⟨6503623222848935063888959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138743962087443948029631125 6503623222848935063888959)
        ·
          refine ⟨9755434834273402595833439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6503623222848935063888959 9755434834273402595833439)
          ·
            refine ⟨14633152251410103893750159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9755434834273402595833439 14633152251410103893750159)
            ·
              refine ⟨21949728377115155840625239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14633152251410103893750159 21949728377115155840625239)
              ·
                refine ⟨32924592565672733760937859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21949728377115155840625239 32924592565672733760937859)
                ·
                  refine ⟨49386888848509100641406789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32924592565672733760937859 49386888848509100641406789)
                  ·
                    refine ⟨9260041659095456370263773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49386888848509100641406789 9260041659095456370263773)
                    ·
                      refine ⟨3472515622160796138848915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9260041659095456370263773 3472515622160796138848915)
                      ·
                        rfl

theorem cell23_6762700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6762700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762700 prefixEnd_6762700 := by exact prefixLift 6762700
  have htrace : WordTrace (prefixWord ++ tailWord_6762700) baseStart_6762700 baseEnd_6762700 := by
    simpa [prefixWord, tailWord_6762700, baseEnd_6762700] using wordTrace_append hprefix tailTrace_6762700
  have hstable : (prefixWord ++ tailWord_6762700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762700).length < 2 ^ (prefixWord ++ tailWord_6762700).sum := by decide
  have hdescent : baseEnd_6762700 < baseStart_6762700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762730 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_6762730 : Nat := 118140960795 + 6762730 * 2 ^ 59
def prefixEnd_6762730 : Nat := 4983230072969 + 3 ^ 40 * 6762730 * 2
def baseEnd_6762730 : Nat := 3472531026580431021473777

theorem tailTrace_6762730 : CollatzResearch.WordTrace tailWord_6762730 prefixEnd_6762730 3472531026580431021473777 := by
  unfold tailWord_6762730
  simp only [CollatzResearch.WordTrace]
  refine ⟨61664256697447916794067411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164438017859861111450846429 61664256697447916794067411)
  ·
    refine ⟨92496385046171875191101117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61664256697447916794067411 92496385046171875191101117)
    ·
      refine ⟨34686144392314453196662919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92496385046171875191101117 34686144392314453196662919)
      ·
        refine ⟨52029216588471679794994379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34686144392314453196662919 52029216588471679794994379)
        ·
          refine ⟨78043824882707519692491569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52029216588471679794994379 78043824882707519692491569)
          ·
            refine ⟨58532868662030639769368677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78043824882707519692491569 58532868662030639769368677)
            ·
              refine ⟨10974912874130744956756627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58532868662030639769368677 10974912874130744956756627)
              ·
                refine ⟨16462369311196117435134941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10974912874130744956756627 16462369311196117435134941)
                ·
                  refine ⟨6173388491698544038175603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16462369311196117435134941 6173388491698544038175603)
                  ·
                    refine ⟨9260082737547816057263405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6173388491698544038175603 9260082737547816057263405)
                    ·
                      refine ⟨3472531026580431021473777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9260082737547816057263405 3472531026580431021473777)
                      ·
                        rfl

theorem cell23_6762730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_6762730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762730 prefixEnd_6762730 := by exact prefixLift 6762730
  have htrace : WordTrace (prefixWord ++ tailWord_6762730) baseStart_6762730 baseEnd_6762730 := by
    simpa [prefixWord, tailWord_6762730, baseEnd_6762730] using wordTrace_append hprefix tailTrace_6762730
  have hstable : (prefixWord ++ tailWord_6762730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762730).length < 2 ^ (prefixWord ++ tailWord_6762730).sum := by decide
  have hdescent : baseEnd_6762730 < baseStart_6762730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762736 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 4]
def baseStart_6762736 : Nat := 118140960795 + 6762736 * 2 ^ 59
def prefixEnd_6762736 : Nat := 4983230072969 + 3 ^ 40 * 6762736 * 2
def baseEnd_6762736 : Nat := 3472534107464357997998749

theorem tailTrace_6762736 : CollatzResearch.WordTrace tailWord_6762736 prefixEnd_6762736 3472534107464357997998749 := by
  unfold tailWord_6762736
  simp only [CollatzResearch.WordTrace]
  refine ⟨123328622813884965100494031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164438163751846620133992041 123328622813884965100494031)
  ·
    refine ⟨184992934220827447650741047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123328622813884965100494031 184992934220827447650741047)
    ·
      refine ⟨277489401331241171476111571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184992934220827447650741047 277489401331241171476111571)
      ·
        refine ⟨416234101996861757214167357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277489401331241171476111571 416234101996861757214167357)
        ·
          refine ⟨156087788248823158955312759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416234101996861757214167357 156087788248823158955312759)
          ·
            refine ⟨234131682373234738432969139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156087788248823158955312759 234131682373234738432969139)
            ·
              refine ⟨351197523559852107649453709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234131682373234738432969139 351197523559852107649453709)
              ·
                refine ⟨131699071334944540368545141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351197523559852107649453709 131699071334944540368545141)
                ·
                  refine ⟨12346787937651050659551107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131699071334944540368545141 12346787937651050659551107)
                  ·
                    refine ⟨18520181906476575989326661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12346787937651050659551107 18520181906476575989326661)
                    ·
                      refine ⟨3472534107464357997998749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18520181906476575989326661 3472534107464357997998749)
                      ·
                        rfl

theorem cell23_6762736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_6762736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762736 prefixEnd_6762736 := by exact prefixLift 6762736
  have htrace : WordTrace (prefixWord ++ tailWord_6762736) baseStart_6762736 baseEnd_6762736 := by
    simpa [prefixWord, tailWord_6762736, baseEnd_6762736] using wordTrace_append hprefix tailTrace_6762736
  have hstable : (prefixWord ++ tailWord_6762736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762736).length < 2 ^ (prefixWord ++ tailWord_6762736).sum := by decide
  have hdescent : baseEnd_6762736 < baseStart_6762736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762750 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_6762750 : Nat := 118140960795 + 6762750 * 2 ^ 59
def prefixEnd_6762750 : Nat := 4983230072969 + 3 ^ 40 * 6762750 * 2
def baseEnd_6762750 : Nat := 1157513765397840314407895

theorem tailTrace_6762750 : CollatzResearch.WordTrace tailWord_6762750 prefixEnd_6762750 1157513765397840314407895 := by
  unfold tailWord_6762750
  simp only [CollatzResearch.WordTrace]
  refine ⟨30832219531214901323999713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164438504166479473727998469 30832219531214901323999713)
  ·
    refine ⟨23124164648411175992999785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30832219531214901323999713 23124164648411175992999785)
    ·
      refine ⟨17343123486308381994749839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23124164648411175992999785 17343123486308381994749839)
      ·
        refine ⟨26014685229462572992124759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17343123486308381994749839 26014685229462572992124759)
        ·
          refine ⟨39022027844193859488187139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26014685229462572992124759 39022027844193859488187139)
          ·
            refine ⟨58533041766290789232280709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39022027844193859488187139 58533041766290789232280709)
            ·
              refine ⟨10974945331179522981052633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58533041766290789232280709 10974945331179522981052633)
              ·
                refine ⟨8231208998384642235789475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10974945331179522981052633 8231208998384642235789475)
                ·
                  refine ⟨12346813497576963353684213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8231208998384642235789475 12346813497576963353684213)
                  ·
                    refine ⟨1157513765397840314407895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12346813497576963353684213 1157513765397840314407895)
                    ·
                      rfl

theorem cell23_6762750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_6762750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762750 prefixEnd_6762750 := by exact prefixLift 6762750
  have htrace : WordTrace (prefixWord ++ tailWord_6762750) baseStart_6762750 baseEnd_6762750 := by
    simpa [prefixWord, tailWord_6762750, baseEnd_6762750] using wordTrace_append hprefix tailTrace_6762750
  have hstable : (prefixWord ++ tailWord_6762750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762750).length < 2 ^ (prefixWord ++ tailWord_6762750).sum := by decide
  have hdescent : baseEnd_6762750 < baseStart_6762750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762753 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_6762753 : Nat := 118140960795 + 6762753 * 2 ^ 59
def prefixEnd_6762753 : Nat := 4983230072969 + 3 ^ 40 * 6762753 * 2
def baseEnd_6762753 : Nat := 3472542836635484431486171

theorem tailTrace_6762753 : CollatzResearch.WordTrace tailWord_6762753 prefixEnd_6762753 3472542836635484431486171 := by
  unfold tailWord_6762753
  simp only [CollatzResearch.WordTrace]
  refine ⟨246657865668708342104356913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164438577112472228069571275 246657865668708342104356913)
  ·
    refine ⟨184993399251531256578267685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246657865668708342104356913 184993399251531256578267685)
    ·
      refine ⟨34686262359662110608425191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184993399251531256578267685 34686262359662110608425191)
      ·
        refine ⟨52029393539493165912637787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34686262359662110608425191 52029393539493165912637787)
        ·
          refine ⟨78044090309239748868956681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52029393539493165912637787 78044090309239748868956681)
          ·
            refine ⟨58533067731929811651717511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78044090309239748868956681 58533067731929811651717511)
            ·
              refine ⟨87799601597894717477576267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58533067731929811651717511 87799601597894717477576267)
              ·
                refine ⟨131699402396842076216364401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87799601597894717477576267 131699402396842076216364401)
                ·
                  refine ⟨98774551797631557162273301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131699402396842076216364401 98774551797631557162273301)
                  ·
                    refine ⟨4630057115513979241981561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98774551797631557162273301 4630057115513979241981561)
                    ·
                      refine ⟨3472542836635484431486171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630057115513979241981561 3472542836635484431486171)
                      ·
                        rfl

theorem cell23_6762753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_6762753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762753 prefixEnd_6762753 := by exact prefixLift 6762753
  have htrace : WordTrace (prefixWord ++ tailWord_6762753) baseStart_6762753 baseEnd_6762753 := by
    simpa [prefixWord, tailWord_6762753, baseEnd_6762753] using wordTrace_append hprefix tailTrace_6762753
  have hstable : (prefixWord ++ tailWord_6762753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762753).length < 2 ^ (prefixWord ++ tailWord_6762753).sum := by decide
  have hdescent : baseEnd_6762753 < baseStart_6762753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762781 : List Nat := [1, 4, 2, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_6762781 : Nat := 118140960795 + 6762781 * 2 ^ 59
def prefixEnd_6762781 : Nat := 4983230072969 + 3 ^ 40 * 6762781 * 2
def baseEnd_6762781 : Nat := 3472557214093810321936043

theorem tailTrace_6762781 : CollatzResearch.WordTrace tailWord_6762781 prefixEnd_6762781 3472557214093810321936043 := by
  unfold tailWord_6762781
  simp only [CollatzResearch.WordTrace]
  refine ⟨246658886912606902886376197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164439257941737935257584131 246658886912606902886376197)
  ·
    refine ⟨46248541296113794291195537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246658886912606902886376197 46248541296113794291195537)
    ·
      refine ⟨34686405972085345718396653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46248541296113794291195537 34686405972085345718396653)
      ·
        refine ⟨13007402239532004644398745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34686405972085345718396653 13007402239532004644398745)
        ·
          refine ⟨9755551679649003483299059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13007402239532004644398745 9755551679649003483299059)
          ·
            refine ⟨14633327519473505224948589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9755551679649003483299059 14633327519473505224948589)
            ·
              refine ⟨5487497819802564459355721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14633327519473505224948589 5487497819802564459355721)
              ·
                refine ⟨4115623364851923344516791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5487497819802564459355721 4115623364851923344516791)
                ·
                  refine ⟨6173435047277885016775187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115623364851923344516791 6173435047277885016775187)
                  ·
                    refine ⟨9260152570916827525162781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6173435047277885016775187 9260152570916827525162781)
                    ·
                      refine ⟨3472557214093810321936043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9260152570916827525162781 3472557214093810321936043)
                      ·
                        rfl

theorem cell23_6762781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_6762781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762781 prefixEnd_6762781 := by exact prefixLift 6762781
  have htrace : WordTrace (prefixWord ++ tailWord_6762781) baseStart_6762781 baseEnd_6762781 := by
    simpa [prefixWord, tailWord_6762781, baseEnd_6762781] using wordTrace_append hprefix tailTrace_6762781
  have hstable : (prefixWord ++ tailWord_6762781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762781).length < 2 ^ (prefixWord ++ tailWord_6762781).sum := by decide
  have hdescent : baseEnd_6762781 < baseStart_6762781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762803 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 3]
def baseStart_6762803 : Nat := 118140960795 + 6762803 * 2 ^ 59
def prefixEnd_6762803 : Nat := 4983230072969 + 3 ^ 40 * 6762803 * 2
def baseEnd_6762803 : Nat := 3472568510668209235860941

theorem tailTrace_6762803 : CollatzResearch.WordTrace tailWord_6762803 prefixEnd_6762803 3472568510668209235860941 := by
  unfold tailWord_6762803
  simp only [CollatzResearch.WordTrace]
  refine ⟨246659689318527200643677063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164439792879018133762451375 246659689318527200643677063)
  ·
    refine ⟨369989533977790800965515595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246659689318527200643677063 369989533977790800965515595)
    ·
      refine ⟨554984300966686201448273393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369989533977790800965515595 554984300966686201448273393)
      ·
        refine ⟨416238225725014651086205045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554984300966686201448273393 416238225725014651086205045)
        ·
          refine ⟨39022333661720123539331723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 416238225725014651086205045 39022333661720123539331723)
          ·
            refine ⟨58533500492580185308997585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39022333661720123539331723 58533500492580185308997585)
            ·
              refine ⟨43900125369435138981748189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58533500492580185308997585 43900125369435138981748189)
              ·
                refine ⟨16462547013538177118155571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43900125369435138981748189 16462547013538177118155571)
                ·
                  refine ⟨24693820520307265677233357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16462547013538177118155571 24693820520307265677233357)
                  ·
                    refine ⟨9260182695115224628962509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24693820520307265677233357 9260182695115224628962509)
                    ·
                      refine ⟨3472568510668209235860941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9260182695115224628962509 3472568510668209235860941)
                      ·
                        rfl

theorem cell23_6762803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_6762803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762803 prefixEnd_6762803 := by exact prefixLift 6762803
  have htrace : WordTrace (prefixWord ++ tailWord_6762803) baseStart_6762803 baseEnd_6762803 := by
    simpa [prefixWord, tailWord_6762803, baseEnd_6762803] using wordTrace_append hprefix tailTrace_6762803
  have hstable : (prefixWord ++ tailWord_6762803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762803).length < 2 ^ (prefixWord ++ tailWord_6762803).sum := by decide
  have hdescent : baseEnd_6762803 < baseStart_6762803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762816 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 5]
def baseStart_6762816 : Nat := 118140960795 + 6762816 * 2 ^ 59
def prefixEnd_6762816 : Nat := 4983230072969 + 3 ^ 40 * 6762816 * 2
def baseEnd_6762816 : Nat := 3472575185916717684998381

theorem tailTrace_6762816 : CollatzResearch.WordTrace tailWord_6762816 prefixEnd_6762816 3472575185916717684998381 := by
  unfold tailWord_6762816
  simp only [CollatzResearch.WordTrace]
  refine ⟨123330081733740051931950151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164440108978320069242600201 123330081733740051931950151)
  ·
    refine ⟨184995122600610077897925227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123330081733740051931950151 184995122600610077897925227)
    ·
      refine ⟨277492683900915116846887841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184995122600610077897925227 277492683900915116846887841)
      ·
        refine ⟨208119512925686337635165881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277492683900915116846887841 208119512925686337635165881)
        ·
          refine ⟨156089634694264753226374411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208119512925686337635165881 156089634694264753226374411)
          ·
            refine ⟨234134452041397129839561617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156089634694264753226374411 234134452041397129839561617)
            ·
              refine ⟨175600839031047847379671213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234134452041397129839561617 175600839031047847379671213)
              ·
                refine ⟨65850314636642942767376705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175600839031047847379671213 65850314636642942767376705)
                ·
                  refine ⟨49387735977482207075532529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65850314636642942767376705 49387735977482207075532529)
                  ·
                    refine ⟨37040801983111655306649397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49387735977482207075532529 37040801983111655306649397)
                    ·
                      refine ⟨3472575185916717684998381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37040801983111655306649397 3472575185916717684998381)
                      ·
                        rfl

theorem cell23_6762816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_6762816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762816 prefixEnd_6762816 := by exact prefixLift 6762816
  have htrace : WordTrace (prefixWord ++ tailWord_6762816) baseStart_6762816 baseEnd_6762816 := by
    simpa [prefixWord, tailWord_6762816, baseEnd_6762816] using wordTrace_append hprefix tailTrace_6762816
  have hstable : (prefixWord ++ tailWord_6762816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762816).length < 2 ^ (prefixWord ++ tailWord_6762816).sum := by decide
  have hdescent : baseEnd_6762816 < baseStart_6762816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762853 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_6762853 : Nat := 118140960795 + 6762853 * 2 ^ 59
def prefixEnd_6762853 : Nat := 4983230072969 + 3 ^ 40 * 6762853 * 2
def baseEnd_6762853 : Nat := 1157531394900311346745237

theorem tailTrace_6762853 : CollatzResearch.WordTrace tailWord_6762853 prefixEnd_6762853 1157531394900311346745237 := by
  unfold tailWord_6762853
  simp only [CollatzResearch.WordTrace]
  refine ⟨246661512968346059182997213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164441008645564039455331475 246661512968346059182997213)
  ·
    refine ⟨92498067363129772193623955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246661512968346059182997213 92498067363129772193623955)
    ·
      refine ⟨138747101044694658290435933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92498067363129772193623955 138747101044694658290435933)
      ·
        refine ⟨52030162891760496858913475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138747101044694658290435933 52030162891760496858913475)
        ·
          refine ⟨78045244337640745288370213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52030162891760496858913475 78045244337640745288370213)
          ·
            refine ⟨14633483313307639741569415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78045244337640745288370213 14633483313307639741569415)
            ·
              refine ⟨21950224969961459612354123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14633483313307639741569415 21950224969961459612354123)
              ·
                refine ⟨32925337454942189418531185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21950224969961459612354123 32925337454942189418531185)
                ·
                  refine ⟨24694003091206642063898389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32925337454942189418531185 24694003091206642063898389)
                  ·
                    refine ⟨1157531394900311346745237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24694003091206642063898389 1157531394900311346745237)
                    ·
                      rfl

theorem cell23_6762853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_6762853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762853 prefixEnd_6762853 := by exact prefixLift 6762853
  have htrace : WordTrace (prefixWord ++ tailWord_6762853) baseStart_6762853 baseEnd_6762853 := by
    simpa [prefixWord, tailWord_6762853, baseEnd_6762853] using wordTrace_append hprefix tailTrace_6762853
  have hstable : (prefixWord ++ tailWord_6762853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762853).length < 2 ^ (prefixWord ++ tailWord_6762853).sum := by decide
  have hdescent : baseEnd_6762853 < baseStart_6762853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762881 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_6762881 : Nat := 118140960795 + 6762881 * 2 ^ 59
def prefixEnd_6762881 : Nat := 4983230072969 + 3 ^ 40 * 6762881 * 2
def baseEnd_6762881 : Nat := 3472608562159259930685583

theorem tailTrace_6762881 : CollatzResearch.WordTrace tailWord_6762881 prefixEnd_6762881 3472608562159259930685583 := by
  unfold tailWord_6762881
  simp only [CollatzResearch.WordTrace]
  refine ⟨246662534212244619965016497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164441689474829746643344331 246662534212244619965016497)
  ·
    refine ⟨184996900659183464973762373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246662534212244619965016497 184996900659183464973762373)
    ·
      refine ⟨34686918873596899682580445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184996900659183464973762373 34686918873596899682580445)
      ·
        refine ⟨13007594577598837380967667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34686918873596899682580445 13007594577598837380967667)
        ·
          refine ⟨19511391866398256071451501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13007594577598837380967667 19511391866398256071451501)
          ·
            refine ⟨7316771949899346026794313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19511391866398256071451501 7316771949899346026794313)
            ·
              refine ⟨5487578962424509520095735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7316771949899346026794313 5487578962424509520095735)
              ·
                refine ⟨8231368443636764280143603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487578962424509520095735 8231368443636764280143603)
                ·
                  refine ⟨12347052665455146420215405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8231368443636764280143603 12347052665455146420215405)
                  ·
                    refine ⟨4630144749545679907580777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12347052665455146420215405 4630144749545679907580777)
                    ·
                      refine ⟨3472608562159259930685583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630144749545679907580777 3472608562159259930685583)
                      ·
                        rfl

theorem cell23_6762881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_6762881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762881 prefixEnd_6762881 := by exact prefixLift 6762881
  have htrace : WordTrace (prefixWord ++ tailWord_6762881) baseStart_6762881 baseEnd_6762881 := by
    simpa [prefixWord, tailWord_6762881, baseEnd_6762881] using wordTrace_append hprefix tailTrace_6762881
  have hstable : (prefixWord ++ tailWord_6762881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762881).length < 2 ^ (prefixWord ++ tailWord_6762881).sum := by decide
  have hdescent : baseEnd_6762881 < baseStart_6762881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762894 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6762894 : Nat := 118140960795 + 6762894 * 2 ^ 59
def prefixEnd_6762894 : Nat := 4983230072969 + 3 ^ 40 * 6762894 * 2
def baseEnd_6762894 : Nat := 3472615237407768379823023

theorem tailTrace_6762894 : CollatzResearch.WordTrace tailWord_6762894 prefixEnd_6762894 3472615237407768379823023 := by
  unfold tailWord_6762894
  simp only [CollatzResearch.WordTrace]
  refine ⟨30832876045149690398154967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164442005574131682123493157 30832876045149690398154967)
  ·
    refine ⟨46249314067724535597232451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30832876045149690398154967 46249314067724535597232451)
    ·
      refine ⟨69373971101586803395848677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46249314067724535597232451 69373971101586803395848677)
      ·
        refine ⟨13007619581547525636721627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69373971101586803395848677 13007619581547525636721627)
        ·
          refine ⟨19511429372321288455082441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13007619581547525636721627 19511429372321288455082441)
          ·
            refine ⟨14633572029240966341311831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19511429372321288455082441 14633572029240966341311831)
            ·
              refine ⟨21950358043861449511967747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14633572029240966341311831 21950358043861449511967747)
              ·
                refine ⟨32925537065792174267951621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21950358043861449511967747 32925537065792174267951621)
                ·
                  refine ⟨6173538199836032675240929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32925537065792174267951621 6173538199836032675240929)
                  ·
                    refine ⟨4630153649877024506430697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6173538199836032675240929 4630153649877024506430697)
                    ·
                      refine ⟨3472615237407768379823023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630153649877024506430697 3472615237407768379823023)
                      ·
                        rfl

theorem cell23_6762894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6762894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762894 prefixEnd_6762894 := by exact prefixLift 6762894
  have htrace : WordTrace (prefixWord ++ tailWord_6762894) baseStart_6762894 baseEnd_6762894 := by
    simpa [prefixWord, tailWord_6762894, baseEnd_6762894] using wordTrace_append hprefix tailTrace_6762894
  have hstable : (prefixWord ++ tailWord_6762894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762894).length < 2 ^ (prefixWord ++ tailWord_6762894).sum := by decide
  have hdescent : baseEnd_6762894 < baseStart_6762894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762896 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 11]
def baseStart_6762896 : Nat := 118140960795 + 6762896 * 2 ^ 59
def prefixEnd_6762896 : Nat := 4983230072969 + 3 ^ 40 * 6762896 * 2
def baseEnd_6762896 : Nat := 1157538754789692457332671

theorem tailTrace_6762896 : CollatzResearch.WordTrace tailWord_6762896 prefixEnd_6762896 1157538754789692457332671 := by
  unfold tailWord_6762896
  simp only [CollatzResearch.WordTrace]
  refine ⟨123331540653595138763406271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164442054204793518351208361 123331540653595138763406271)
  ·
    refine ⟨184997310980392708145109407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123331540653595138763406271 184997310980392708145109407)
    ·
      refine ⟨277495966470589062217664111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184997310980392708145109407 277495966470589062217664111)
      ·
        refine ⟨416243949705883593326496167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277495966470589062217664111 416243949705883593326496167)
        ·
          refine ⟨624365924558825389989744251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416243949705883593326496167 624365924558825389989744251)
          ·
            refine ⟨936548886838238084984616377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624365924558825389989744251 936548886838238084984616377)
            ·
              refine ⟨702411665128678563738462283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936548886838238084984616377 702411665128678563738462283)
              ·
                refine ⟨1053617497693017845607693425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702411665128678563738462283 1053617497693017845607693425)
                ·
                  refine ⟨790213123269763384205770069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1053617497693017845607693425 790213123269763384205770069)
                  ·
                    refine ⟨1157538754789692457332671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 790213123269763384205770069 1157538754789692457332671)
                    ·
                      rfl

theorem cell23_6762896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 11].length) (baseStart_6762896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762896 prefixEnd_6762896 := by exact prefixLift 6762896
  have htrace : WordTrace (prefixWord ++ tailWord_6762896) baseStart_6762896 baseEnd_6762896 := by
    simpa [prefixWord, tailWord_6762896, baseEnd_6762896] using wordTrace_append hprefix tailTrace_6762896
  have hstable : (prefixWord ++ tailWord_6762896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762896).length < 2 ^ (prefixWord ++ tailWord_6762896).sum := by decide
  have hdescent : baseEnd_6762896 < baseStart_6762896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6762970 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_6762970 : Nat := 118140960795 + 6762970 * 2 ^ 59
def prefixEnd_6762970 : Nat := 4983230072969 + 3 ^ 40 * 6762970 * 2
def baseEnd_6762970 : Nat := 3472654261937510082472673

theorem tailTrace_6762970 : CollatzResearch.WordTrace tailWord_6762970 prefixEnd_6762970 3472654261937510082472673 := by
  unfold tailWord_6762970
  simp only [CollatzResearch.WordTrace]
  refine ⟨61666445077230547041251591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164443853539281458776670909 61666445077230547041251591)
  ·
    refine ⟨92499667615845820561877387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61666445077230547041251591 92499667615845820561877387)
    ·
      refine ⟨138749501423768730842816081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92499667615845820561877387 138749501423768730842816081)
      ·
        refine ⟨104062126067826548132112061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138749501423768730842816081 104062126067826548132112061)
        ·
          refine ⟨39023297275434955549542023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104062126067826548132112061 39023297275434955549542023)
          ·
            refine ⟨58534945913152433324313035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39023297275434955549542023 58534945913152433324313035)
            ·
              refine ⟨87802418869728649986469553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58534945913152433324313035 87802418869728649986469553)
              ·
                refine ⟨65851814152296487489852165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87802418869728649986469553 65851814152296487489852165)
                ·
                  refine ⟨12347215153555591404347281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65851814152296487489852165 12347215153555591404347281)
                  ·
                    refine ⟨9260411365166693553260461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12347215153555591404347281 9260411365166693553260461)
                    ·
                      refine ⟨3472654261937510082472673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9260411365166693553260461 3472654261937510082472673)
                      ·
                        rfl

theorem cell23_6762970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_6762970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6762970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6762970 prefixEnd_6762970 := by exact prefixLift 6762970
  have htrace : WordTrace (prefixWord ++ tailWord_6762970) baseStart_6762970 baseEnd_6762970 := by
    simpa [prefixWord, tailWord_6762970, baseEnd_6762970] using wordTrace_append hprefix tailTrace_6762970
  have hstable : (prefixWord ++ tailWord_6762970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6762970).length < 2 ^ (prefixWord ++ tailWord_6762970).sum := by decide
  have hdescent : baseEnd_6762970 < baseStart_6762970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6762970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763003 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 7, 5]
def baseStart_6763003 : Nat := 118140960795 + 6763003 * 2 ^ 59
def prefixEnd_6763003 : Nat := 4983230072969 + 3 ^ 40 * 6763003 * 2
def baseEnd_6763003 : Nat := 1157557068933036151120007

theorem tailTrace_6763003 : CollatzResearch.WordTrace tailWord_6763003 prefixEnd_6763003 1157557068933036151120007 := by
  unfold tailWord_6763003
  simp only [CollatzResearch.WordTrace]
  refine ⟨246666983917802634800957663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164444655945201756533971775 246666983917802634800957663)
  ·
    refine ⟨370000475876703952201436495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246666983917802634800957663 370000475876703952201436495)
    ·
      refine ⟨555000713815055928302154743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370000475876703952201436495 555000713815055928302154743)
      ·
        refine ⟨832501070722583892453232115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555000713815055928302154743 832501070722583892453232115)
        ·
          refine ⟨1248751606083875838679848173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832501070722583892453232115 1248751606083875838679848173)
          ·
            refine ⟨468281852281453439504943065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1248751606083875838679848173 468281852281453439504943065)
            ·
              refine ⟨351211389211090079628707299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468281852281453439504943065 351211389211090079628707299)
              ·
                refine ⟨526817083816635119443060949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351211389211090079628707299 526817083816635119443060949)
                ·
                  refine ⟨12347275401952385611946741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 526817083816635119443060949 12347275401952385611946741)
                  ·
                    refine ⟨1157557068933036151120007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12347275401952385611946741 1157557068933036151120007)
                    ·
                      rfl

theorem cell23_6763003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 5].length) (baseStart_6763003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763003 prefixEnd_6763003 := by exact prefixLift 6763003
  have htrace : WordTrace (prefixWord ++ tailWord_6763003) baseStart_6763003 baseEnd_6763003 := by
    simpa [prefixWord, tailWord_6763003, baseEnd_6763003] using wordTrace_append hprefix tailTrace_6763003
  have hstable : (prefixWord ++ tailWord_6763003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763003).length < 2 ^ (prefixWord ++ tailWord_6763003).sum := by decide
  have hdescent : baseEnd_6763003 < baseStart_6763003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763020 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_6763020 : Nat := 118140960795 + 6763020 * 2 ^ 59
def prefixEnd_6763020 : Nat := 4983230072969 + 3 ^ 40 * 6763020 * 2
def baseEnd_6763020 : Nat := 1157559978656744962282481

theorem tailTrace_6763020 : CollatzResearch.WordTrace tailWord_6763020 prefixEnd_6763020 1157559978656744962282481 := by
  unfold tailWord_6763020
  simp only [CollatzResearch.WordTrace]
  refine ⟨123333801979370523352163257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164445069305827364469551009 123333801979370523352163257)
  ·
    refine ⟨92500351484527892514122443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123333801979370523352163257 92500351484527892514122443)
    ·
      refine ⟨138750527226791838771183665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92500351484527892514122443 138750527226791838771183665)
      ·
        refine ⟨104062895420093879078387749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138750527226791838771183665 104062895420093879078387749)
        ·
          refine ⟨19511792891267602327197703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104062895420093879078387749 19511792891267602327197703)
          ·
            refine ⟨29267689336901403490796555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19511792891267602327197703 29267689336901403490796555)
            ·
              refine ⟨43901534005352105236194833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29267689336901403490796555 43901534005352105236194833)
              ·
                refine ⟨32926150504014078927146125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43901534005352105236194833 32926150504014078927146125)
                ·
                  refine ⟨12347306439005279597679797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32926150504014078927146125 12347306439005279597679797)
                  ·
                    refine ⟨1157559978656744962282481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12347306439005279597679797 1157559978656744962282481)
                    ·
                      rfl

theorem cell23_6763020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_6763020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763020 prefixEnd_6763020 := by exact prefixLift 6763020
  have htrace : WordTrace (prefixWord ++ tailWord_6763020) baseStart_6763020 baseEnd_6763020 := by
    simpa [prefixWord, tailWord_6763020, baseEnd_6763020] using wordTrace_append hprefix tailTrace_6763020
  have hstable : (prefixWord ++ tailWord_6763020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763020).length < 2 ^ (prefixWord ++ tailWord_6763020).sum := by decide
  have hdescent : baseEnd_6763020 < baseStart_6763020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763023 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_6763023 : Nat := 118140960795 + 6763023 * 2 ^ 59
def prefixEnd_6763023 : Nat := 4983230072969 + 3 ^ 40 * 6763023 * 2
def baseEnd_6763023 : Nat := 3472681476412198375109929

theorem tailTrace_6763023 : CollatzResearch.WordTrace tailWord_6763023 prefixEnd_6763023 3472681476412198375109929 := by
  unfold tailWord_6763023
  simp only [CollatzResearch.WordTrace]
  refine ⟨246667713377730178216685723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164445142251820118811123815 246667713377730178216685723)
  ·
    refine ⟨370001570066595267325028585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246667713377730178216685723 370001570066595267325028585)
    ·
      refine ⟨277501177549946450493771439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370001570066595267325028585 277501177549946450493771439)
      ·
        refine ⟨416251766324919675740657159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277501177549946450493771439 416251766324919675740657159)
        ·
          refine ⟨624377649487379513610985739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416251766324919675740657159 624377649487379513610985739)
          ·
            refine ⟨936566474231069270416478609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624377649487379513610985739 936566474231069270416478609)
            ·
              refine ⟨702424855673301952812358957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936566474231069270416478609 702424855673301952812358957)
              ·
                refine ⟨263409320877488232304634609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 702424855673301952812358957 263409320877488232304634609)
                ·
                  refine ⟨197556990658116174228475957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263409320877488232304634609 197556990658116174228475957)
                  ·
                    refine ⟨18520967874198391333919621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 197556990658116174228475957 18520967874198391333919621)
                    ·
                      refine ⟨3472681476412198375109929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18520967874198391333919621 3472681476412198375109929)
                      ·
                        rfl

theorem cell23_6763023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_6763023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763023 prefixEnd_6763023 := by exact prefixLift 6763023
  have htrace : WordTrace (prefixWord ++ tailWord_6763023) baseStart_6763023 baseEnd_6763023 := by
    simpa [prefixWord, tailWord_6763023, baseEnd_6763023] using wordTrace_append hprefix tailTrace_6763023
  have hstable : (prefixWord ++ tailWord_6763023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763023).length < 2 ^ (prefixWord ++ tailWord_6763023).sum := by decide
  have hdescent : baseEnd_6763023 < baseStart_6763023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763033 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 5, 6]
def baseStart_6763033 : Nat := 118140960795 + 6763033 * 2 ^ 59
def prefixEnd_6763033 : Nat := 4983230072969 + 3 ^ 40 * 6763033 * 2
def baseEnd_6763033 : Nat := 1157562203739581111994961

theorem tailTrace_6763033 : CollatzResearch.WordTrace tailWord_6763033 prefixEnd_6763033 1157562203739581111994961 := by
  unfold tailWord_6763033
  simp only [CollatzResearch.WordTrace]
  refine ⟨246668078107693949924549753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164445385405129299949699835 246668078107693949924549753)
  ·
    refine ⟨185001058580770462443412315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246668078107693949924549753 185001058580770462443412315)
    ·
      refine ⟨277501587871155693665118473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185001058580770462443412315 277501587871155693665118473)
      ·
        refine ⟨208126190903366770248838855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277501587871155693665118473 208126190903366770248838855)
        ·
          refine ⟨312189286355050155373258283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208126190903366770248838855 312189286355050155373258283)
          ·
            refine ⟨468283929532575233059887425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312189286355050155373258283 468283929532575233059887425)
            ·
              refine ⟨351212947149431424794915569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468283929532575233059887425 351212947149431424794915569)
              ·
                refine ⟨263409710362073568596186677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351212947149431424794915569 263409710362073568596186677)
                ·
                  refine ⟨24694660346444397055892501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263409710362073568596186677 24694660346444397055892501)
                  ·
                    refine ⟨1157562203739581111994961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24694660346444397055892501 1157562203739581111994961)
                    ·
                      rfl

theorem cell23_6763033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_6763033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763033 prefixEnd_6763033 := by exact prefixLift 6763033
  have htrace : WordTrace (prefixWord ++ tailWord_6763033) baseStart_6763033 baseEnd_6763033 := by
    simpa [prefixWord, tailWord_6763033, baseEnd_6763033] using wordTrace_append hprefix tailTrace_6763033
  have hstable : (prefixWord ++ tailWord_6763033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763033).length < 2 ^ (prefixWord ++ tailWord_6763033).sum := by decide
  have hdescent : baseEnd_6763033 < baseStart_6763033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763054 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_6763054 : Nat := 118140960795 + 6763054 * 2 ^ 59
def prefixEnd_6763054 : Nat := 4983230072969 + 3 ^ 40 * 6763054 * 2
def baseEnd_6763054 : Nat := 1157565798104162584607429

theorem tailTrace_6763054 : CollatzResearch.WordTrace tailWord_6763054 prefixEnd_6763054 1157565798104162584607429 := by
  unfold tailWord_6763054
  simp only [CollatzResearch.WordTrace]
  refine ⟨30833605505077233813883027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164445896027078580340709477 30833605505077233813883027)
  ·
    refine ⟨46250408257615850720824541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30833605505077233813883027 46250408257615850720824541)
    ·
      refine ⟨17343903096605944020309203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46250408257615850720824541 17343903096605944020309203)
      ·
        refine ⟨26015854644908916030463805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17343903096605944020309203 26015854644908916030463805)
        ·
          refine ⟨9755945491840843511423927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26015854644908916030463805 9755945491840843511423927)
          ·
            refine ⟨14633918237761265267135891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9755945491840843511423927 14633918237761265267135891)
            ·
              refine ⟨21950877356641897900703837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14633918237761265267135891 21950877356641897900703837)
              ·
                refine ⟨8231579008740711712763939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21950877356641897900703837 8231579008740711712763939)
                ·
                  refine ⟨12347368513111067569145909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8231579008740711712763939 12347368513111067569145909)
                  ·
                    refine ⟨1157565798104162584607429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12347368513111067569145909 1157565798104162584607429)
                    ·
                      rfl

theorem cell23_6763054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_6763054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763054 prefixEnd_6763054 := by exact prefixLift 6763054
  have htrace : WordTrace (prefixWord ++ tailWord_6763054) baseStart_6763054 baseEnd_6763054 := by
    simpa [prefixWord, tailWord_6763054, baseEnd_6763054] using wordTrace_append hprefix tailTrace_6763054
  have hstable : (prefixWord ++ tailWord_6763054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763054).length < 2 ^ (prefixWord ++ tailWord_6763054).sum := by decide
  have hdescent : baseEnd_6763054 < baseStart_6763054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763063 : List Nat := [1, 1, 3, 1, 2, 3, 12]
def baseStart_6763063 : Nat := 118140960795 + 6763063 * 2 ^ 59
def prefixEnd_6763063 : Nat := 4983230072969 + 3 ^ 40 * 6763063 * 2
def baseEnd_6763063 : Nat := 42872864390597261958145

theorem tailTrace_6763063 : CollatzResearch.WordTrace tailWord_6763063 prefixEnd_6763063 42872864390597261958145 := by
  unfold tailWord_6763063
  simp only [CollatzResearch.WordTrace]
  refine ⟨246669172297585265048141843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164446114865056843365427895 246669172297585265048141843)
  ·
    refine ⟨370003758446377897572212765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246669172297585265048141843 370003758446377897572212765)
    ·
      refine ⟨138751409417391711589579787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370003758446377897572212765 138751409417391711589579787)
      ·
        refine ⟨208127114126087567384369681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138751409417391711589579787 208127114126087567384369681)
        ·
          refine ⟨156095335594565675538277261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208127114126087567384369681 156095335594565675538277261)
          ·
            refine ⟨58535750847962128326853973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156095335594565675538277261 58535750847962128326853973)
            ·
              refine ⟨42872864390597261958145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 58535750847962128326853973 42872864390597261958145)
              ·
                rfl

theorem cell23_6763063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 12].length) (baseStart_6763063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763063 prefixEnd_6763063 := by exact prefixLift 6763063
  have htrace : WordTrace (prefixWord ++ tailWord_6763063) baseStart_6763063 baseEnd_6763063 := by
    simpa [prefixWord, tailWord_6763063, baseEnd_6763063] using wordTrace_append hprefix tailTrace_6763063
  have hstable : (prefixWord ++ tailWord_6763063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763063).length < 2 ^ (prefixWord ++ tailWord_6763063).sum := by decide
  have hdescent : baseEnd_6763063 < baseStart_6763063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763084 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 2, 4]
def baseStart_6763084 : Nat := 118140960795 + 6763084 * 2 ^ 59
def prefixEnd_6763084 : Nat := 4983230072969 + 3 ^ 40 * 6763084 * 2
def baseEnd_6763084 : Nat := 1157570932910707545482383

theorem tailTrace_6763084 : CollatzResearch.WordTrace tailWord_6763084 prefixEnd_6763084 1157570932910707545482383 := by
  unfold tailWord_6763084
  simp only [CollatzResearch.WordTrace]
  refine ⟨123334969115254592817328153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164446625487006123756437537 123334969115254592817328153)
  ·
    refine ⟨92501226836440944612996115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123334969115254592817328153 92501226836440944612996115)
    ·
      refine ⟨138751840254661416919494173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92501226836440944612996115 138751840254661416919494173)
      ·
        refine ⟨52031940095498031344810315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138751840254661416919494173 52031940095498031344810315)
        ·
          refine ⟨78047910143247047017215473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52031940095498031344810315 78047910143247047017215473)
          ·
            refine ⟨58535932607435285262911605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78047910143247047017215473 58535932607435285262911605)
            ·
              refine ⟨5487743681947057993397963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58535932607435285262911605 5487743681947057993397963)
              ·
                refine ⟨8231615522920586990096945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487743681947057993397963 8231615522920586990096945)
                ·
                  refine ⟨6173711642190440242572709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8231615522920586990096945 6173711642190440242572709)
                  ·
                    refine ⟨1157570932910707545482383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173711642190440242572709 1157570932910707545482383)
                    ·
                      rfl

theorem cell23_6763084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_6763084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763084 prefixEnd_6763084 := by exact prefixLift 6763084
  have htrace : WordTrace (prefixWord ++ tailWord_6763084) baseStart_6763084 baseEnd_6763084 := by
    simpa [prefixWord, tailWord_6763084, baseEnd_6763084] using wordTrace_append hprefix tailTrace_6763084
  have hstable : (prefixWord ++ tailWord_6763084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763084).length < 2 ^ (prefixWord ++ tailWord_6763084).sum := by decide
  have hdescent : baseEnd_6763084 < baseStart_6763084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763107 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 3]
def baseStart_6763107 : Nat := 118140960795 + 6763107 * 2 ^ 59
def prefixEnd_6763107 : Nat := 4983230072969 + 3 ^ 40 * 6763107 * 2
def baseEnd_6763107 : Nat := 3472724608787176046459543

theorem tailTrace_6763107 : CollatzResearch.WordTrace tailWord_6763107 prefixEnd_6763107 3472724608787176046459543 := by
  unfold tailWord_6763107
  simp only [CollatzResearch.WordTrace]
  refine ⟨246670777109425860562743575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164447184739617240375162383 246670777109425860562743575)
  ·
    refine ⟨370006165664138790844115363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246670777109425860562743575 370006165664138790844115363)
    ·
      refine ⟨555009248496208186266173045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370006165664138790844115363 555009248496208186266173045)
      ·
        refine ⟨52032117046519517462453723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 555009248496208186266173045 52032117046519517462453723)
        ·
          refine ⟨78048175569779276193680585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52032117046519517462453723 78048175569779276193680585)
          ·
            refine ⟨58536131677334457145260439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78048175569779276193680585 58536131677334457145260439)
            ·
              refine ⟨87804197516001685717890659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58536131677334457145260439 87804197516001685717890659)
              ·
                refine ⟨131706296274002528576835989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87804197516001685717890659 131706296274002528576835989)
                ·
                  refine ⟨6173732637843868527039187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131706296274002528576835989 6173732637843868527039187)
                  ·
                    refine ⟨9260598956765802790558781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6173732637843868527039187 9260598956765802790558781)
                    ·
                      refine ⟨3472724608787176046459543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9260598956765802790558781 3472724608787176046459543)
                      ·
                        rfl

theorem cell23_6763107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_6763107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763107 prefixEnd_6763107 := by exact prefixLift 6763107
  have htrace : WordTrace (prefixWord ++ tailWord_6763107) baseStart_6763107 baseEnd_6763107 := by
    simpa [prefixWord, tailWord_6763107, baseEnd_6763107] using wordTrace_append hprefix tailTrace_6763107
  have hstable : (prefixWord ++ tailWord_6763107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763107).length < 2 ^ (prefixWord ++ tailWord_6763107).sum := by decide
  have hdescent : baseEnd_6763107 < baseStart_6763107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763125 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6763125 : Nat := 118140960795 + 6763125 * 2 ^ 59
def prefixEnd_6763125 : Nat := 4983230072969 + 3 ^ 40 * 6763125 * 2
def baseEnd_6763125 : Nat := 3472733851438956976034461

theorem tailTrace_6763125 : CollatzResearch.WordTrace tailWord_6763125 prefixEnd_6763125 3472733851438956976034461 := by
  unfold tailWord_6763125
  simp only [CollatzResearch.WordTrace]
  refine ⟨246671433623360649636898829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164447622415573766424599219 246671433623360649636898829)
  ·
    refine ⟨92501787608760243613837061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246671433623360649636898829 92501787608760243613837061)
    ·
      refine ⟨17344085176642545677594449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92501787608760243613837061 17344085176642545677594449)
      ·
        refine ⟨13008063882481909258195837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17344085176642545677594449 13008063882481909258195837)
        ·
          refine ⟨4878023955930715971823439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13008063882481909258195837 4878023955930715971823439)
          ·
            refine ⟨7317035933896073957735159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4878023955930715971823439 7317035933896073957735159)
            ·
              refine ⟨10975553900844110936602739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7317035933896073957735159 10975553900844110936602739)
              ·
                refine ⟨16463330851266166404904109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10975553900844110936602739 16463330851266166404904109)
                ·
                  refine ⟨6173749069224812401839041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16463330851266166404904109 6173749069224812401839041)
                  ·
                    refine ⟨4630311801918609301379281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6173749069224812401839041 4630311801918609301379281)
                    ·
                      refine ⟨3472733851438956976034461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630311801918609301379281 3472733851438956976034461)
                      ·
                        rfl

theorem cell23_6763125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6763125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763125 prefixEnd_6763125 := by exact prefixLift 6763125
  have htrace : WordTrace (prefixWord ++ tailWord_6763125) baseStart_6763125 baseEnd_6763125 := by
    simpa [prefixWord, tailWord_6763125, baseEnd_6763125] using wordTrace_append hprefix tailTrace_6763125
  have hstable : (prefixWord ++ tailWord_6763125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763125).length < 2 ^ (prefixWord ++ tailWord_6763125).sum := by decide
  have hdescent : baseEnd_6763125 < baseStart_6763125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763141 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 2, 1, 3]
def baseStart_6763141 : Nat := 118140960795 + 6763141 * 2 ^ 59
def prefixEnd_6763141 : Nat := 4983230072969 + 3 ^ 40 * 6763141 * 2
def baseEnd_6763141 : Nat := 3472742067129428913434387

theorem tailTrace_6763141 : CollatzResearch.WordTrace tailWord_6763141 prefixEnd_6763141 3472742067129428913434387 := by
  unfold tailWord_6763141
  simp only [CollatzResearch.WordTrace]
  refine ⟨246672017191302684369481277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164448011460868456246320851 246672017191302684369481277)
  ·
    refine ⟨92502006446738506638555479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246672017191302684369481277 92502006446738506638555479)
    ·
      refine ⟨138753009670107759957833219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92502006446738506638555479 138753009670107759957833219)
      ·
        refine ⟨208129514505161639936749829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138753009670107759957833219 208129514505161639936749829)
        ·
          refine ⟨39024283969717807488140593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208129514505161639936749829 39024283969717807488140593)
          ·
            refine ⟨29268212977288355616105445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39024283969717807488140593 29268212977288355616105445)
            ·
              refine ⟨5487789933241566678019771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29268212977288355616105445 5487789933241566678019771)
              ·
                refine ⟨8231684899862350017029657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487789933241566678019771 8231684899862350017029657)
                ·
                  refine ⟨6173763674896762512772243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8231684899862350017029657 6173763674896762512772243)
                  ·
                    refine ⟨9260645512345143769158365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6173763674896762512772243 9260645512345143769158365)
                    ·
                      refine ⟨3472742067129428913434387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9260645512345143769158365 3472742067129428913434387)
                      ·
                        rfl

theorem cell23_6763141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_6763141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763141 prefixEnd_6763141 := by exact prefixLift 6763141
  have htrace : WordTrace (prefixWord ++ tailWord_6763141) baseStart_6763141 baseEnd_6763141 := by
    simpa [prefixWord, tailWord_6763141, baseEnd_6763141] using wordTrace_append hprefix tailTrace_6763141
  have hstable : (prefixWord ++ tailWord_6763141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763141).length < 2 ^ (prefixWord ++ tailWord_6763141).sum := by decide
  have hdescent : baseEnd_6763141 < baseStart_6763141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763164 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_6763164 : Nat := 118140960795 + 6763164 * 2 ^ 59
def prefixEnd_6763164 : Nat := 4983230072969 + 3 ^ 40 * 6763164 * 2
def baseEnd_6763164 : Nat := 3472753877184482323446781

theorem tailTrace_6763164 : CollatzResearch.WordTrace tailWord_6763164 prefixEnd_6763164 3472753877184482323446781 := by
  unfold tailWord_6763164
  simp only [CollatzResearch.WordTrace]
  refine ⟨123336428035109679648784273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164448570713479572865045697 123336428035109679648784273)
  ·
    refine ⟨92502321026332259736588205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123336428035109679648784273 92502321026332259736588205)
    ·
      refine ⟨34688370384874597401220577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92502321026332259736588205 34688370384874597401220577)
      ·
        refine ⟨26016277788655948050915433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34688370384874597401220577 26016277788655948050915433)
        ·
          refine ⟨19512208341491961038186575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26016277788655948050915433 19512208341491961038186575)
          ·
            refine ⟨29268312512237941557279863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19512208341491961038186575 29268312512237941557279863)
            ·
              refine ⟨43902468768356912335919795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29268312512237941557279863 43902468768356912335919795)
              ·
                refine ⟨65853703152535368503879693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43902468768356912335919795 65853703152535368503879693)
                ·
                  refine ⟨24695138682200763188954885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65853703152535368503879693 24695138682200763188954885)
                  ·
                    refine ⟨4630338502912643097929041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24695138682200763188954885 4630338502912643097929041)
                    ·
                      refine ⟨3472753877184482323446781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630338502912643097929041 3472753877184482323446781)
                      ·
                        rfl

theorem cell23_6763164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_6763164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763164 prefixEnd_6763164 := by exact prefixLift 6763164
  have htrace : WordTrace (prefixWord ++ tailWord_6763164) baseStart_6763164 baseEnd_6763164 := by
    simpa [prefixWord, tailWord_6763164, baseEnd_6763164] using wordTrace_append hprefix tailTrace_6763164
  have hstable : (prefixWord ++ tailWord_6763164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763164).length < 2 ^ (prefixWord ++ tailWord_6763164).sum := by decide
  have hdescent : baseEnd_6763164 < baseStart_6763164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763168 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 1, 3, 2]
def baseStart_6763168 : Nat := 118140960795 + 6763168 * 2 ^ 59
def prefixEnd_6763168 : Nat := 4983230072969 + 3 ^ 40 * 6763168 * 2
def baseEnd_6763168 : Nat := 3472755931107100307796763

theorem tailTrace_6763168 : CollatzResearch.WordTrace tailWord_6763168 prefixEnd_6763168 3472755931107100307796763 := by
  unfold tailWord_6763168
  simp only [CollatzResearch.WordTrace]
  refine ⟨123336500981102433990357079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164448667974803245320476105 123336500981102433990357079)
  ·
    refine ⟨185004751471653650985535619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123336500981102433990357079 185004751471653650985535619)
    ·
      refine ⟨277507127207480476478303429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185004751471653650985535619 277507127207480476478303429)
      ·
        refine ⟨52032586351402589339681893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277507127207480476478303429 52032586351402589339681893)
        ·
          refine ⟨9756109940887985501190355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52032586351402589339681893 9756109940887985501190355)
          ·
            refine ⟨14634164911331978251785533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9756109940887985501190355 14634164911331978251785533)
            ·
              refine ⟨5487811841749491844419575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14634164911331978251785533 5487811841749491844419575)
              ·
                refine ⟨8231717762624237766629363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487811841749491844419575 8231717762624237766629363)
                ·
                  refine ⟨12347576643936356649944045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8231717762624237766629363 12347576643936356649944045)
                  ·
                    refine ⟨4630341241476133743729017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12347576643936356649944045 4630341241476133743729017)
                    ·
                      refine ⟨3472755931107100307796763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630341241476133743729017 3472755931107100307796763)
                      ·
                        rfl

theorem cell23_6763168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_6763168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763168 prefixEnd_6763168 := by exact prefixLift 6763168
  have htrace : WordTrace (prefixWord ++ tailWord_6763168) baseStart_6763168 baseEnd_6763168 := by
    simpa [prefixWord, tailWord_6763168, baseEnd_6763168] using wordTrace_append hprefix tailTrace_6763168
  have hstable : (prefixWord ++ tailWord_6763168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763168).length < 2 ^ (prefixWord ++ tailWord_6763168).sum := by decide
  have hdescent : baseEnd_6763168 < baseStart_6763168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763197 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_6763197 : Nat := 118140960795 + 6763197 * 2 ^ 59
def prefixEnd_6763197 : Nat := 4983230072969 + 3 ^ 40 * 6763197 * 2
def baseEnd_6763197 : Nat := 3472770822046080694334129

theorem tailTrace_6763197 : CollatzResearch.WordTrace tailWord_6763197 prefixEnd_6763197 3472770822046080694334129 := by
  unfold tailWord_6763197
  simp only [CollatzResearch.WordTrace]
  refine ⟨246674059679099805933519845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164449373119399870622346563 246674059679099805933519845)
  ·
    refine ⟨46251386189831213612534971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246674059679099805933519845 46251386189831213612534971)
    ·
      refine ⟨69377079284746820418802457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46251386189831213612534971 69377079284746820418802457)
      ·
        refine ⟨52032809463560115314101843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69377079284746820418802457 52032809463560115314101843)
        ·
          refine ⟨78049214195340172971152765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52032809463560115314101843 78049214195340172971152765)
          ·
            refine ⟨29268455323252564864182287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78049214195340172971152765 29268455323252564864182287)
            ·
              refine ⟨43902682984878847296273431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29268455323252564864182287 43902682984878847296273431)
              ·
                refine ⟨65854024477318270944410147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43902682984878847296273431 65854024477318270944410147)
                ·
                  refine ⟨98781036715977406416615221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65854024477318270944410147 98781036715977406416615221)
                  ·
                    refine ⟨9260722192122881851557677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98781036715977406416615221 9260722192122881851557677)
                    ·
                      refine ⟨3472770822046080694334129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9260722192122881851557677 3472770822046080694334129)
                      ·
                        rfl

theorem cell23_6763197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_6763197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763197 prefixEnd_6763197 := by exact prefixLift 6763197
  have htrace : WordTrace (prefixWord ++ tailWord_6763197) baseStart_6763197 baseEnd_6763197 := by
    simpa [prefixWord, tailWord_6763197, baseEnd_6763197] using wordTrace_append hprefix tailTrace_6763197
  have hstable : (prefixWord ++ tailWord_6763197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763197).length < 2 ^ (prefixWord ++ tailWord_6763197).sum := by decide
  have hdescent : baseEnd_6763197 < baseStart_6763197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763274 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_6763274 : Nat := 118140960795 + 6763274 * 2 ^ 59
def prefixEnd_6763274 : Nat := 4983230072969 + 3 ^ 40 * 6763274 * 2
def baseEnd_6763274 : Nat := 3472810360056476893071275

theorem tailTrace_6763274 : CollatzResearch.WordTrace tailWord_6763274 prefixEnd_6763274 3472810360056476893071275 := by
  unfold tailWord_6763274
  simp only [CollatzResearch.WordTrace]
  refine ⟨61669217024955212021018219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164451245399880565389381917 61669217024955212021018219)
  ·
    refine ⟨92503825537432818031527329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61669217024955212021018219 92503825537432818031527329)
    ·
      refine ⟨69377869153074613523645497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92503825537432818031527329 69377869153074613523645497)
      ·
        refine ⟨52033401864805960142734123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69377869153074613523645497 52033401864805960142734123)
        ·
          refine ⟨78050102797208940214101185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52033401864805960142734123 78050102797208940214101185)
          ·
            refine ⟨58537577097906705160575889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78050102797208940214101185 58537577097906705160575889)
            ·
              refine ⟨43903182823430028870431917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58537577097906705160575889 43903182823430028870431917)
              ·
                refine ⟨16463693558786260826411969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43903182823430028870431917 16463693558786260826411969)
                ·
                  refine ⟨12347770169089695619808977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16463693558786260826411969 12347770169089695619808977)
                  ·
                    refine ⟨9260827626817271714856733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12347770169089695619808977 9260827626817271714856733)
                    ·
                      refine ⟨3472810360056476893071275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9260827626817271714856733 3472810360056476893071275)
                      ·
                        rfl

theorem cell23_6763274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_6763274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763274 prefixEnd_6763274 := by exact prefixLift 6763274
  have htrace : WordTrace (prefixWord ++ tailWord_6763274) baseStart_6763274 baseEnd_6763274 := by
    simpa [prefixWord, tailWord_6763274, baseEnd_6763274] using wordTrace_append hprefix tailTrace_6763274
  have hstable : (prefixWord ++ tailWord_6763274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763274).length < 2 ^ (prefixWord ++ tailWord_6763274).sum := by decide
  have hdescent : baseEnd_6763274 < baseStart_6763274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763281 : List Nat := [1, 2, 2, 1, 1, 3, 5, 3, 1, 4]
def baseStart_6763281 : Nat := 118140960795 + 6763281 * 2 ^ 59
def prefixEnd_6763281 : Nat := 4983230072969 + 3 ^ 40 * 6763281 * 2
def baseEnd_6763281 : Nat := 1157604651473686121894581

theorem tailTrace_6763281 : CollatzResearch.WordTrace tailWord_6763281 prefixEnd_6763281 1157604651473686121894581 := by
  unfold tailWord_6763281
  simp only [CollatzResearch.WordTrace]
  refine ⟨246677123410795488279577697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164451415607196992186385131 246677123410795488279577697)
  ·
    refine ⟨185007842558096616209683273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246677123410795488279577697 185007842558096616209683273)
    ·
      refine ⟨138755881918572462157262455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185007842558096616209683273 138755881918572462157262455)
      ·
        refine ⟨208133822877858693235893683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138755881918572462157262455 208133822877858693235893683)
        ·
          refine ⟨312200734316788039853840525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208133822877858693235893683 312200734316788039853840525)
          ·
            refine ⟨117075275368795514945190197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312200734316788039853840525 117075275368795514945190197)
            ·
              refine ⟨10975807065824579526111581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117075275368795514945190197 10975807065824579526111581)
              ·
                refine ⟨4115927649684217322291843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10975807065824579526111581 4115927649684217322291843)
                ·
                  refine ⟨6173891474526325983437765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115927649684217322291843 6173891474526325983437765)
                  ·
                    refine ⟨1157604651473686121894581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173891474526325983437765 1157604651473686121894581)
                    ·
                      rfl

theorem cell23_6763281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_6763281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763281 prefixEnd_6763281 := by exact prefixLift 6763281
  have htrace : WordTrace (prefixWord ++ tailWord_6763281) baseStart_6763281 baseEnd_6763281 := by
    simpa [prefixWord, tailWord_6763281, baseEnd_6763281] using wordTrace_append hprefix tailTrace_6763281
  have hstable : (prefixWord ++ tailWord_6763281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763281).length < 2 ^ (prefixWord ++ tailWord_6763281).sum := by decide
  have hdescent : baseEnd_6763281 < baseStart_6763281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763331 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 2, 3, 2]
def baseStart_6763331 : Nat := 118140960795 + 6763331 * 2 ^ 59
def prefixEnd_6763331 : Nat := 4983230072969 + 3 ^ 40 * 6763331 * 2
def baseEnd_6763331 : Nat := 3472839628453783170058513

theorem tailTrace_6763331 : CollatzResearch.WordTrace tailWord_6763331 prefixEnd_6763331 3472839628453783170058513 := by
  unfold tailWord_6763331
  simp only [CollatzResearch.WordTrace]
  refine ⟨246678947060614346818897847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164452631373742897879265231 246678947060614346818897847)
  ·
    refine ⟨370018420590921520228346771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246678947060614346818897847 370018420590921520228346771)
    ·
      refine ⟨555027630886382280342520157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370018420590921520228346771 555027630886382280342520157)
      ·
        refine ⟨208135361582393355128445059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555027630886382280342520157 208135361582393355128445059)
        ·
          refine ⟨312203042373590032692667589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208135361582393355128445059 312203042373590032692667589)
          ·
            refine ⟨58538070445048131129875173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312203042373590032692667589 58538070445048131129875173)
            ·
              refine ⟨10975888208446524586851595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58538070445048131129875173 10975888208446524586851595)
              ·
                refine ⟨16463832312669786880277393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10975888208446524586851595 16463832312669786880277393)
                ·
                  refine ⟨12347874234502340160208045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16463832312669786880277393 12347874234502340160208045)
                  ·
                    refine ⟨4630452837938377560078017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12347874234502340160208045 4630452837938377560078017)
                    ·
                      refine ⟨3472839628453783170058513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630452837938377560078017 3472839628453783170058513)
                      ·
                        rfl

theorem cell23_6763331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_6763331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763331 prefixEnd_6763331 := by exact prefixLift 6763331
  have htrace : WordTrace (prefixWord ++ tailWord_6763331) baseStart_6763331 baseEnd_6763331 := by
    simpa [prefixWord, tailWord_6763331, baseEnd_6763331] using wordTrace_append hprefix tailTrace_6763331
  have hstable : (prefixWord ++ tailWord_6763331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763331).length < 2 ^ (prefixWord ++ tailWord_6763331).sum := by decide
  have hdescent : baseEnd_6763331 < baseStart_6763331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763337 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 3, 6]
def baseStart_6763337 : Nat := 118140960795 + 6763337 * 2 ^ 59
def prefixEnd_6763337 : Nat := 4983230072969 + 3 ^ 40 * 6763337 * 2
def baseEnd_6763337 : Nat := 1157614236445903382194495

theorem tailTrace_6763337 : CollatzResearch.WordTrace tailWord_6763337 prefixEnd_6763337 1157614236445903382194495 := by
  unfold tailWord_6763337
  simp only [CollatzResearch.WordTrace]
  refine ⟨246679165898592609843616265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164452777265728406562410843 246679165898592609843616265)
  ·
    refine ⟨185009374423944457382712199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246679165898592609843616265 185009374423944457382712199)
    ·
      refine ⟨277514061635916686074068299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185009374423944457382712199 277514061635916686074068299)
      ·
        refine ⟨416271092453875029111102449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277514061635916686074068299 416271092453875029111102449)
        ·
          refine ⟨312203319340406271833326837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416271092453875029111102449 312203319340406271833326837)
          ·
            refine ⟨29269061188163087984374391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 312203319340406271833326837 29269061188163087984374391)
            ·
              refine ⟨43903591782244631976561587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29269061188163087984374391 43903591782244631976561587)
              ·
                refine ⟨65855387673366947964842381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43903591782244631976561587 65855387673366947964842381)
                ·
                  refine ⟨24695770377512605486815893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65855387673366947964842381 24695770377512605486815893)
                  ·
                    refine ⟨1157614236445903382194495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24695770377512605486815893 1157614236445903382194495)
                    ·
                      rfl

theorem cell23_6763337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_6763337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763337 prefixEnd_6763337 := by exact prefixLift 6763337
  have htrace : WordTrace (prefixWord ++ tailWord_6763337) baseStart_6763337 baseEnd_6763337 := by
    simpa [prefixWord, tailWord_6763337, baseEnd_6763337] using wordTrace_append hprefix tailTrace_6763337
  have hstable : (prefixWord ++ tailWord_6763337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763337).length < 2 ^ (prefixWord ++ tailWord_6763337).sum := by decide
  have hdescent : baseEnd_6763337 < baseStart_6763337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763344 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 4]
def baseStart_6763344 : Nat := 118140960795 + 6763344 * 2 ^ 59
def prefixEnd_6763344 : Nat := 4983230072969 + 3 ^ 40 * 6763344 * 2
def baseEnd_6763344 : Nat := 3472846303702291619195953

theorem tailTrace_6763344 : CollatzResearch.WordTrace tailWord_6763344 prefixEnd_6763344 3472846303702291619195953 := by
  unfold tailWord_6763344
  simp only [CollatzResearch.WordTrace]
  refine ⟨123339710604783625019560543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164452947473044833359414057 123339710604783625019560543)
  ·
    refine ⟨185009565907175437529340815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123339710604783625019560543 185009565907175437529340815)
    ·
      refine ⟨277514348860763156294011223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185009565907175437529340815 277514348860763156294011223)
      ·
        refine ⟨416271523291144734441016835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277514348860763156294011223 416271523291144734441016835)
        ·
          refine ⟨624407284936717101661525253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416271523291144734441016835 624407284936717101661525253)
          ·
            refine ⟨117076365925634456561535985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 624407284936717101661525253 117076365925634456561535985)
            ·
              refine ⟨87807274444225842421151989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117076365925634456561535985 87807274444225842421151989)
              ·
                refine ⟨8231931979146172726982999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87807274444225842421151989 8231931979146172726982999)
                ·
                  refine ⟨12347897968719259090474499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8231931979146172726982999 12347897968719259090474499)
                  ·
                    refine ⟨18521846953078888635711749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12347897968719259090474499 18521846953078888635711749)
                    ·
                      refine ⟨3472846303702291619195953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18521846953078888635711749 3472846303702291619195953)
                      ·
                        rfl

theorem cell23_6763344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 4].length) (baseStart_6763344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763344 prefixEnd_6763344 := by exact prefixLift 6763344
  have htrace : WordTrace (prefixWord ++ tailWord_6763344) baseStart_6763344 baseEnd_6763344 := by
    simpa [prefixWord, tailWord_6763344, baseEnd_6763344] using wordTrace_append hprefix tailTrace_6763344
  have hstable : (prefixWord ++ tailWord_6763344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763344).length < 2 ^ (prefixWord ++ tailWord_6763344).sum := by decide
  have hdescent : baseEnd_6763344 < baseStart_6763344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763381 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_6763381 : Nat := 118140960795 + 6763381 * 2 ^ 59
def prefixEnd_6763381 : Nat := 4983230072969 + 3 ^ 40 * 6763381 * 2
def baseEnd_6763381 : Nat := 3472865302486507974433283

theorem tailTrace_6763381 : CollatzResearch.WordTrace tailWord_6763381 prefixEnd_6763381 3472865302486507974433283 := by
  unfold tailWord_6763381
  simp only [CollatzResearch.WordTrace]
  refine ⟨246680770710433205358217997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164453847140288803572145331 246680770710433205358217997)
  ·
    refine ⟨92505289016412452009331749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246680770710433205358217997 92505289016412452009331749)
    ·
      refine ⟨17344741690577334751749703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92505289016412452009331749 17344741690577334751749703)
      ·
        refine ⟨26017112535866002127624555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17344741690577334751749703 26017112535866002127624555)
        ·
          refine ⟨39025668803799003191436833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26017112535866002127624555 39025668803799003191436833)
          ·
            refine ⟨29269251602849252393577625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39025668803799003191436833 29269251602849252393577625)
            ·
              refine ⟨21951938702136939295183219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29269251602849252393577625 21951938702136939295183219)
              ·
                refine ⟨32927908053205408942774829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21951938702136939295183219 32927908053205408942774829)
                ·
                  refine ⟨12347965519952028353540561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32927908053205408942774829 12347965519952028353540561)
                  ·
                    refine ⟨9260974139964021265155421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12347965519952028353540561 9260974139964021265155421)
                    ·
                      refine ⟨3472865302486507974433283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9260974139964021265155421 3472865302486507974433283)
                      ·
                        rfl

theorem cell23_6763381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_6763381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763381 prefixEnd_6763381 := by exact prefixLift 6763381
  have htrace : WordTrace (prefixWord ++ tailWord_6763381) baseStart_6763381 baseEnd_6763381 := by
    simpa [prefixWord, tailWord_6763381, baseEnd_6763381] using wordTrace_append hprefix tailTrace_6763381
  have hstable : (prefixWord ++ tailWord_6763381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763381).length < 2 ^ (prefixWord ++ tailWord_6763381).sum := by decide
  have hdescent : baseEnd_6763381 < baseStart_6763381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763395 : List Nat := [1, 1, 1, 3, 4, 1, 4, 3, 1, 2, 2]
def baseStart_6763395 : Nat := 118140960795 + 6763395 * 2 ^ 59
def prefixEnd_6763395 : Nat := 4983230072969 + 3 ^ 40 * 6763395 * 2
def baseEnd_6763395 : Nat := 3472872491215670919658219

theorem tailTrace_6763395 : CollatzResearch.WordTrace tailWord_6763395 prefixEnd_6763395 3472872491215670919658219 := by
  unfold tailWord_6763395
  simp only [CollatzResearch.WordTrace]
  refine ⟨246681281332382485749227639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164454187554921657166151759 246681281332382485749227639)
  ·
    refine ⟨370021921998573728623841459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246681281332382485749227639 370021921998573728623841459)
    ·
      refine ⟨555032882997860592935762189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370021921998573728623841459 555032882997860592935762189)
      ·
        refine ⟨208137331124197722350910821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555032882997860592935762189 208137331124197722350910821)
        ·
          refine ⟨39025749585787072940795779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208137331124197722350910821 39025749585787072940795779)
          ·
            refine ⟨58538624378680609411193669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39025749585787072940795779 58538624378680609411193669)
            ·
              refine ⟨10975992071002614264598813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58538624378680609411193669 10975992071002614264598813)
              ·
                refine ⟨4115997026625980349224555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10975992071002614264598813 4115997026625980349224555)
                ·
                  refine ⟨6173995539938970523836833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115997026625980349224555 6173995539938970523836833)
                  ·
                    refine ⟨4630496654954227892877625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6173995539938970523836833 4630496654954227892877625)
                    ·
                      refine ⟨3472872491215670919658219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630496654954227892877625 3472872491215670919658219)
                      ·
                        rfl

theorem cell23_6763395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 1, 2, 2].length) (baseStart_6763395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763395 prefixEnd_6763395 := by exact prefixLift 6763395
  have htrace : WordTrace (prefixWord ++ tailWord_6763395) baseStart_6763395 baseEnd_6763395 := by
    simpa [prefixWord, tailWord_6763395, baseEnd_6763395] using wordTrace_append hprefix tailTrace_6763395
  have hstable : (prefixWord ++ tailWord_6763395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763395).length < 2 ^ (prefixWord ++ tailWord_6763395).sum := by decide
  have hdescent : baseEnd_6763395 < baseStart_6763395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763411 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 3]
def baseStart_6763411 : Nat := 118140960795 + 6763411 * 2 ^ 59
def prefixEnd_6763411 : Nat := 4983230072969 + 3 ^ 40 * 6763411 * 2
def baseEnd_6763411 : Nat := 3472880706906142857058145

theorem tailTrace_6763411 : CollatzResearch.WordTrace tailWord_6763411 prefixEnd_6763411 3472880706906142857058145 := by
  unfold tailWord_6763411
  simp only [CollatzResearch.WordTrace]
  refine ⟨246681864900324520481810087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164454576600216346987873391 246681864900324520481810087)
  ·
    refine ⟨370022797350486780722715131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246681864900324520481810087 370022797350486780722715131)
    ·
      refine ⟨555034196025730171084072697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370022797350486780722715131 555034196025730171084072697)
      ·
        refine ⟨416275647019297628313054523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555034196025730171084072697 416275647019297628313054523)
        ·
          refine ⟨624413470528946442469581785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416275647019297628313054523 624413470528946442469581785)
          ·
            refine ⟨468310102896709831852186339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624413470528946442469581785 468310102896709831852186339)
            ·
              refine ⟨702465154345064747778279509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468310102896709831852186339 702465154345064747778279509)
              ·
                refine ⟨8232013527481227513026713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 702465154345064747778279509 8232013527481227513026713)
                ·
                  refine ⟨6174010145610920634770035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8232013527481227513026713 6174010145610920634770035)
                  ·
                    refine ⟨9261015218416380952155053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174010145610920634770035 9261015218416380952155053)
                    ·
                      refine ⟨3472880706906142857058145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9261015218416380952155053 3472880706906142857058145)
                      ·
                        rfl

theorem cell23_6763411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 2, 1, 3].length) (baseStart_6763411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763411 prefixEnd_6763411 := by exact prefixLift 6763411
  have htrace : WordTrace (prefixWord ++ tailWord_6763411) baseStart_6763411 baseEnd_6763411 := by
    simpa [prefixWord, tailWord_6763411, baseEnd_6763411] using wordTrace_append hprefix tailTrace_6763411
  have hstable : (prefixWord ++ tailWord_6763411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763411).length < 2 ^ (prefixWord ++ tailWord_6763411).sum := by decide
  have hdescent : baseEnd_6763411 < baseStart_6763411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763468 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 4, 2, 2]
def baseStart_6763468 : Nat := 118140960795 + 6763468 * 2 ^ 59
def prefixEnd_6763468 : Nat := 4983230072969 + 3 ^ 40 * 6763468 * 2
def baseEnd_6763468 : Nat := 3472909975303449134045383

theorem tailTrace_6763468 : CollatzResearch.WordTrace tailWord_6763468 prefixEnd_6763468 3472909975303449134045383 := by
  unfold tailWord_6763468
  simp only [CollatzResearch.WordTrace]
  refine ⟨123341971930559009608317529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164455962574078679477756705 123341971930559009608317529)
  ·
    refine ⟨92506478947919257206238147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123341971930559009608317529 92506478947919257206238147)
    ·
      refine ⟨138759718421878885809357221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92506478947919257206238147 138759718421878885809357221)
      ·
        refine ⟨26017447204102291089254479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138759718421878885809357221 26017447204102291089254479)
        ·
          refine ⟨39026170806153436633881719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26017447204102291089254479 39026170806153436633881719)
          ·
            refine ⟨58539256209230154950822579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39026170806153436633881719 58539256209230154950822579)
            ·
              refine ⟨87808884313845232426233869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58539256209230154950822579 87808884313845232426233869)
              ·
                refine ⟨32928331617691962159837701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87808884313845232426233869 32928331617691962159837701)
                ·
                  refine ⟨6174062178317242904969569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32928331617691962159837701 6174062178317242904969569)
                  ·
                    refine ⟨4630546633737932178727177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6174062178317242904969569 4630546633737932178727177)
                    ·
                      refine ⟨3472909975303449134045383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630546633737932178727177 3472909975303449134045383)
                      ·
                        rfl

theorem cell23_6763468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_6763468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763468 prefixEnd_6763468 := by exact prefixLift 6763468
  have htrace : WordTrace (prefixWord ++ tailWord_6763468) baseStart_6763468 baseEnd_6763468 := by
    simpa [prefixWord, tailWord_6763468, baseEnd_6763468] using wordTrace_append hprefix tailTrace_6763468
  have hstable : (prefixWord ++ tailWord_6763468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763468).length < 2 ^ (prefixWord ++ tailWord_6763468).sum := by decide
  have hdescent : baseEnd_6763468 < baseStart_6763468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763521 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 2, 5]
def baseStart_6763521 : Nat := 118140960795 + 6763521 * 2 ^ 59
def prefixEnd_6763521 : Nat := 4983230072969 + 3 ^ 40 * 6763521 * 2
def baseEnd_6763521 : Nat := 1157645729926045808894213

theorem tailTrace_6763521 : CollatzResearch.WordTrace tailWord_6763521 prefixEnd_6763521 1157645729926045808894213 := by
  unfold tailWord_6763521
  simp only [CollatzResearch.WordTrace]
  refine ⟨246685876929926009268314417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164457251286617339512209611 246685876929926009268314417)
  ·
    refine ⟨185014407697444506951235813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246685876929926009268314417 185014407697444506951235813)
    ·
      refine ⟨34690201443270845053356715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185014407697444506951235813 34690201443270845053356715)
      ·
        refine ⟨52035302164906267580035073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34690201443270845053356715 52035302164906267580035073)
        ·
          refine ⟨39026476623679700685026305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52035302164906267580035073 39026476623679700685026305)
          ·
            refine ⟨29269857467759775513769729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39026476623679700685026305 29269857467759775513769729)
            ·
              refine ⟨21952393100819831635327297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29269857467759775513769729 21952393100819831635327297)
              ·
                refine ⟨16464294825614873726495473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21952393100819831635327297 16464294825614873726495473)
                ·
                  refine ⟨12348221119211155294871605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16464294825614873726495473 12348221119211155294871605)
                  ·
                    refine ⟨1157645729926045808894213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12348221119211155294871605 1157645729926045808894213)
                    ·
                      rfl

theorem cell23_6763521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_6763521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763521 prefixEnd_6763521 := by exact prefixLift 6763521
  have htrace : WordTrace (prefixWord ++ tailWord_6763521) baseStart_6763521 baseEnd_6763521 := by
    simpa [prefixWord, tailWord_6763521, baseEnd_6763521] using wordTrace_append hprefix tailTrace_6763521
  have hstable : (prefixWord ++ tailWord_6763521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763521).length < 2 ^ (prefixWord ++ tailWord_6763521).sum := by decide
  have hdescent : baseEnd_6763521 < baseStart_6763521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763551 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 5, 4]
def baseStart_6763551 : Nat := 118140960795 + 6763551 * 2 ^ 59
def prefixEnd_6763551 : Nat := 4983230072969 + 3 ^ 40 * 6763551 * 2
def baseEnd_6763551 : Nat := 1157650864732590769769167

theorem tailTrace_6763551 : CollatzResearch.WordTrace tailWord_6763551 prefixEnd_6763551 1157650864732590769769167 := by
  unfold tailWord_6763551
  simp only [CollatzResearch.WordTrace]
  refine ⟨246686971119817324391906507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164457980746544882927937671 246686971119817324391906507)
  ·
    refine ⟨370030456679725986587859761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246686971119817324391906507 370030456679725986587859761)
    ·
      refine ⟨277522842509794489940894821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370030456679725986587859761 277522842509794489940894821)
      ·
        refine ⟨52035532970586466863917779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277522842509794489940894821 52035532970586466863917779)
        ·
          refine ⟨78053299455879700295876669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52035532970586466863917779 78053299455879700295876669)
          ·
            refine ⟨29269987295954887610953751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78053299455879700295876669 29269987295954887610953751)
            ·
              refine ⟨43904980943932331416430627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29269987295954887610953751 43904980943932331416430627)
              ·
                refine ⟨65857471415898497124645941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43904980943932331416430627 65857471415898497124645941)
                ·
                  refine ⟨6174137945240484105435557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65857471415898497124645941 6174137945240484105435557)
                  ·
                    refine ⟨1157650864732590769769167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6174137945240484105435557 1157650864732590769769167)
                    ·
                      rfl

theorem cell23_6763551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 5, 4].length) (baseStart_6763551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763551 prefixEnd_6763551 := by exact prefixLift 6763551
  have htrace : WordTrace (prefixWord ++ tailWord_6763551) baseStart_6763551 baseEnd_6763551 := by
    simpa [prefixWord, tailWord_6763551, baseEnd_6763551] using wordTrace_append hprefix tailTrace_6763551
  have hstable : (prefixWord ++ tailWord_6763551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763551).length < 2 ^ (prefixWord ++ tailWord_6763551).sum := by decide
  have hdescent : baseEnd_6763551 < baseStart_6763551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763564 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 8]
def baseStart_6763564 : Nat := 118140960795 + 6763564 * 2 ^ 59
def prefixEnd_6763564 : Nat := 4983230072969 + 3 ^ 40 * 6763564 * 2
def baseEnd_6763564 : Nat := 385884363271808973160549

theorem tailTrace_6763564 : CollatzResearch.WordTrace tailWord_6763564 prefixEnd_6763564 385884363271808973160549 := by
  unfold tailWord_6763564
  simp only [CollatzResearch.WordTrace]
  refine ⟨123343722634385113806064873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164458296845846818408086497 123343722634385113806064873)
  ·
    refine ⟨92507791975788835354548655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123343722634385113806064873 92507791975788835354548655)
    ·
      refine ⟨138761687963683253031822983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92507791975788835354548655 138761687963683253031822983)
      ·
        refine ⟨208142531945524879547734475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138761687963683253031822983 208142531945524879547734475)
        ·
          refine ⟨312213797918287319321601713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208142531945524879547734475 312213797918287319321601713)
          ·
            refine ⟨234160348438715489491201285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312213797918287319321601713 234160348438715489491201285)
            ·
              refine ⟨43905065332259154279600241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234160348438715489491201285 43905065332259154279600241)
              ·
                refine ⟨32928798999194365709700181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43905065332259154279600241 32928798999194365709700181)
                ·
                  refine ⟨385884363271808973160549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32928798999194365709700181 385884363271808973160549)
                  ·
                    rfl

theorem cell23_6763564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 8].length) (baseStart_6763564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763564 prefixEnd_6763564 := by exact prefixLift 6763564
  have htrace : WordTrace (prefixWord ++ tailWord_6763564) baseStart_6763564 baseEnd_6763564 := by
    simpa [prefixWord, tailWord_6763564, baseEnd_6763564] using wordTrace_append hprefix tailTrace_6763564
  have hstable : (prefixWord ++ tailWord_6763564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763564).length < 2 ^ (prefixWord ++ tailWord_6763564).sum := by decide
  have hdescent : baseEnd_6763564 < baseStart_6763564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763581 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 8]
def baseStart_6763581 : Nat := 118140960795 + 6763581 * 2 ^ 59
def prefixEnd_6763581 : Nat := 4983230072969 + 3 ^ 40 * 6763581 * 2
def baseEnd_6763581 : Nat := 385885333179711910214707

theorem tailTrace_6763581 : CollatzResearch.WordTrace tailWord_6763581 prefixEnd_6763581 385885333179711910214707 := by
  unfold tailWord_6763581
  simp only [CollatzResearch.WordTrace]
  refine ⟨246688065309708639515498597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164458710206472426343665731 246688065309708639515498597)
  ·
    refine ⟨46254012245570369909155987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246688065309708639515498597 46254012245570369909155987)
    ·
      refine ⟨69381018368355554863733981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46254012245570369909155987 69381018368355554863733981)
      ·
        refine ⟨26017881888133333073900243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69381018368355554863733981 26017881888133333073900243)
        ·
          refine ⟨39026822832199999610850365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26017881888133333073900243 39026822832199999610850365)
          ·
            refine ⟨14635058562074999854068887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39026822832199999610850365 14635058562074999854068887)
            ·
              refine ⟨21952587843112499781103331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14635058562074999854068887 21952587843112499781103331)
              ·
                refine ⟨32928881764668749671654997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21952587843112499781103331 32928881764668749671654997)
                ·
                  refine ⟨385885333179711910214707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32928881764668749671654997 385885333179711910214707)
                  ·
                    rfl

theorem cell23_6763581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_6763581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763581 prefixEnd_6763581 := by exact prefixLift 6763581
  have htrace : WordTrace (prefixWord ++ tailWord_6763581) baseStart_6763581 baseEnd_6763581 := by
    simpa [prefixWord, tailWord_6763581, baseEnd_6763581] using wordTrace_append hprefix tailTrace_6763581
  have hstable : (prefixWord ++ tailWord_6763581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763581).length < 2 ^ (prefixWord ++ tailWord_6763581).sum := by decide
  have hdescent : baseEnd_6763581 < baseStart_6763581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763584 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_6763584 : Nat := 118140960795 + 6763584 * 2 ^ 59
def prefixEnd_6763584 : Nat := 4983230072969 + 3 ^ 40 * 6763584 * 2
def baseEnd_6763584 : Nat := 3472969539059370680194849

theorem tailTrace_6763584 : CollatzResearch.WordTrace tailWord_6763584 prefixEnd_6763584 3472969539059370680194849 := by
  unfold tailWord_6763584
  simp only [CollatzResearch.WordTrace]
  refine ⟨123344087364348885513928903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164458783152465180685238537 123344087364348885513928903)
  ·
    refine ⟨185016131046523328270893355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123344087364348885513928903 185016131046523328270893355)
    ·
      refine ⟨277524196569784992406340033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185016131046523328270893355 277524196569784992406340033)
      ·
        refine ⟨208143147427338744304755025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277524196569784992406340033 208143147427338744304755025)
        ·
          refine ⟨156107360570504058228566269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208143147427338744304755025 156107360570504058228566269)
          ·
            refine ⟨58540260213939021835712351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156107360570504058228566269 58540260213939021835712351)
            ·
              refine ⟨87810390320908532753568527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58540260213939021835712351 87810390320908532753568527)
              ·
                refine ⟨131715585481362799130352791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87810390320908532753568527 131715585481362799130352791)
                ·
                  refine ⟨197573378222044198695529187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131715585481362799130352791 197573378222044198695529187)
                  ·
                    refine ⟨296360067333066298043293781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 197573378222044198695529187 296360067333066298043293781)
                    ·
                      refine ⟨3472969539059370680194849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 296360067333066298043293781 3472969539059370680194849)
                      ·
                        rfl

theorem cell23_6763584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_6763584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763584 prefixEnd_6763584 := by exact prefixLift 6763584
  have htrace : WordTrace (prefixWord ++ tailWord_6763584) baseStart_6763584 baseEnd_6763584 := by
    simpa [prefixWord, tailWord_6763584, baseEnd_6763584] using wordTrace_append hprefix tailTrace_6763584
  have hstable : (prefixWord ++ tailWord_6763584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763584).length < 2 ^ (prefixWord ++ tailWord_6763584).sum := by decide
  have hdescent : baseEnd_6763584 < baseStart_6763584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763585 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 3, 4]
def baseStart_6763585 : Nat := 118140960795 + 6763585 * 2 ^ 59
def prefixEnd_6763585 : Nat := 4983230072969 + 3 ^ 40 * 6763585 * 2
def baseEnd_6763585 : Nat := 1157656684180008392094115

theorem tailTrace_6763585 : CollatzResearch.WordTrace tailWord_6763585 prefixEnd_6763585 1157656684180008392094115 := by
  unfold tailWord_6763585
  simp only [CollatzResearch.WordTrace]
  refine ⟨246688211201694148198644209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164458807467796098799096139 246688211201694148198644209)
  ·
    refine ⟨185016158401270611148983157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246688211201694148198644209 185016158401270611148983157)
    ·
      refine ⟨17345264850119119795217171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185016158401270611148983157 17345264850119119795217171)
      ·
        refine ⟨26017897275178679692825757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17345264850119119795217171 26017897275178679692825757)
        ·
          refine ⟨9756711478192004884809659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26017897275178679692825757 9756711478192004884809659)
          ·
            refine ⟨14635067217288007327214489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9756711478192004884809659 14635067217288007327214489)
            ·
              refine ⟨10976300412966005495410867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14635067217288007327214489 10976300412966005495410867)
              ·
                refine ⟨16464450619449008243116301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10976300412966005495410867 16464450619449008243116301)
                ·
                  refine ⟨6174168982293378091168613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16464450619449008243116301 6174168982293378091168613)
                  ·
                    refine ⟨1157656684180008392094115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6174168982293378091168613 1157656684180008392094115)
                    ·
                      rfl

theorem cell23_6763585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_6763585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763585 prefixEnd_6763585 := by exact prefixLift 6763585
  have htrace : WordTrace (prefixWord ++ tailWord_6763585) baseStart_6763585 baseEnd_6763585 := by
    simpa [prefixWord, tailWord_6763585, baseEnd_6763585] using wordTrace_append hprefix tailTrace_6763585
  have hstable : (prefixWord ++ tailWord_6763585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763585).length < 2 ^ (prefixWord ++ tailWord_6763585).sum := by decide
  have hdescent : baseEnd_6763585 < baseStart_6763585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763598 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 6]
def baseStart_6763598 : Nat := 118140960795 + 6763598 * 2 ^ 59
def prefixEnd_6763598 : Nat := 4983230072969 + 3 ^ 40 * 6763598 * 2
def baseEnd_6763598 : Nat := 385886303087614847268865

theorem tailTrace_6763598 : CollatzResearch.WordTrace tailWord_6763598 prefixEnd_6763598 385886303087614847268865 := by
  unfold tailWord_6763598
  simp only [CollatzResearch.WordTrace]
  refine ⟨30836085668830881427358431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164459123567098034279244965 30836085668830881427358431)
  ·
    refine ⟨46254128503246322141037647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30836085668830881427358431 46254128503246322141037647)
    ·
      refine ⟨69381192754869483211556471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46254128503246322141037647 69381192754869483211556471)
      ·
        refine ⟨104071789132304224817334707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69381192754869483211556471 104071789132304224817334707)
        ·
          refine ⟨156107683698456337226002061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104071789132304224817334707 156107683698456337226002061)
          ·
            refine ⟨58540381386921126459750773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156107683698456337226002061 58540381386921126459750773)
            ·
              refine ⟨5488160755023855605601635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58540381386921126459750773 5488160755023855605601635)
              ·
                refine ⟨8232241132535783408402453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488160755023855605601635 8232241132535783408402453)
                ·
                  refine ⟨385886303087614847268865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8232241132535783408402453 385886303087614847268865)
                  ·
                    rfl

theorem cell23_6763598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_6763598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763598 prefixEnd_6763598 := by exact prefixLift 6763598
  have htrace : WordTrace (prefixWord ++ tailWord_6763598) baseStart_6763598 baseEnd_6763598 := by
    simpa [prefixWord, tailWord_6763598, baseEnd_6763598] using wordTrace_append hprefix tailTrace_6763598
  have hstable : (prefixWord ++ tailWord_6763598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763598).length < 2 ^ (prefixWord ++ tailWord_6763598).sum := by decide
  have hdescent : baseEnd_6763598 < baseStart_6763598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763608 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 3, 1, 3]
def baseStart_6763608 : Nat := 118140960795 + 6763608 * 2 ^ 59
def prefixEnd_6763608 : Nat := 4983230072969 + 3 ^ 40 * 6763608 * 2
def baseEnd_6763608 : Nat := 3472981862595078586294739

theorem tailTrace_6763608 : CollatzResearch.WordTrace tailWord_6763608 prefixEnd_6763608 3472981862595078586294739 := by
  unfold tailWord_6763608
  simp only [CollatzResearch.WordTrace]
  refine ⟨123344525040305411563365739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164459366720407215417820985 123344525040305411563365739)
  ·
    refine ⟨185016787560458117345048609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123344525040305411563365739 185016787560458117345048609)
    ·
      refine ⟨138762590670343588008786457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185016787560458117345048609 138762590670343588008786457)
      ·
        refine ⟨104071943002757691006589843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138762590670343588008786457 104071943002757691006589843)
        ·
          refine ⟨156107914504136536509884765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104071943002757691006589843 156107914504136536509884765)
          ·
            refine ⟨58540467939051201191206787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156107914504136536509884765 58540467939051201191206787)
            ·
              refine ⟨87810701908576801786810181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58540467939051201191206787 87810701908576801786810181)
              ·
                refine ⟨16464506607858150335026909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87810701908576801786810181 16464506607858150335026909)
                ·
                  refine ⟨6174189977946806375635091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16464506607858150335026909 6174189977946806375635091)
                  ·
                    refine ⟨9261284966920209563452637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174189977946806375635091 9261284966920209563452637)
                    ·
                      refine ⟨3472981862595078586294739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9261284966920209563452637 3472981862595078586294739)
                      ·
                        rfl

theorem cell23_6763608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_6763608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763608 prefixEnd_6763608 := by exact prefixLift 6763608
  have htrace : WordTrace (prefixWord ++ tailWord_6763608) baseStart_6763608 baseEnd_6763608 := by
    simpa [prefixWord, tailWord_6763608, baseEnd_6763608] using wordTrace_append hprefix tailTrace_6763608
  have hstable : (prefixWord ++ tailWord_6763608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763608).length < 2 ^ (prefixWord ++ tailWord_6763608).sum := by decide
  have hdescent : baseEnd_6763608 < baseStart_6763608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763651 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 5]
def baseStart_6763651 : Nat := 118140960795 + 6763651 * 2 ^ 59
def prefixEnd_6763651 : Nat := 4983230072969 + 3 ^ 40 * 6763651 * 2
def baseEnd_6763651 : Nat := 3473003942263221918057041

theorem tailTrace_6763651 : CollatzResearch.WordTrace tailWord_6763651 prefixEnd_6763651 3473003942263221918057041 := by
  unfold tailWord_6763651
  simp only [CollatzResearch.WordTrace]
  refine ⟨246690618419455041470546807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164460412279636694313697871 246690618419455041470546807)
  ·
    refine ⟨370035927629182562205820211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246690618419455041470546807 370035927629182562205820211)
    ·
      refine ⟨555053891443773843308730317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370035927629182562205820211 555053891443773843308730317)
      ·
        refine ⟨208145209291415191240773869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 555053891443773843308730317 208145209291415191240773869)
        ·
          refine ⟨78054453484280696715290201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208145209291415191240773869 78054453484280696715290201)
          ·
            refine ⟨58540840113210522536467651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78054453484280696715290201 58540840113210522536467651)
            ·
              refine ⟨87811260169815783804701477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58540840113210522536467651 87811260169815783804701477)
              ·
                refine ⟨16464611281840459463381527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87811260169815783804701477 16464611281840459463381527)
                ·
                  refine ⟨24696916922760689195072291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16464611281840459463381527 24696916922760689195072291)
                  ·
                    refine ⟨37045375384141033792608437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24696916922760689195072291 37045375384141033792608437)
                    ·
                      refine ⟨3473003942263221918057041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37045375384141033792608437 3473003942263221918057041)
                      ·
                        rfl

theorem cell23_6763651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_6763651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763651 prefixEnd_6763651 := by exact prefixLift 6763651
  have htrace : WordTrace (prefixWord ++ tailWord_6763651) baseStart_6763651 baseEnd_6763651 := by
    simpa [prefixWord, tailWord_6763651, baseEnd_6763651] using wordTrace_append hprefix tailTrace_6763651
  have hstable : (prefixWord ++ tailWord_6763651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763651).length < 2 ^ (prefixWord ++ tailWord_6763651).sum := by decide
  have hdescent : baseEnd_6763651 < baseStart_6763651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763671 : List Nat := [1, 1, 3, 3, 3, 1, 2, 9]
def baseStart_6763671 : Nat := 118140960795 + 6763671 * 2 ^ 59
def prefixEnd_6763671 : Nat := 4983230072969 + 3 ^ 40 * 6763671 * 2
def baseEnd_6763671 : Nat := 128630155995418957029887

theorem tailTrace_6763671 : CollatzResearch.WordTrace tailWord_6763671 prefixEnd_6763671 128630155995418957029887 := by
  unfold tailWord_6763671
  simp only [CollatzResearch.WordTrace]
  refine ⟨246691347879382584886274867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164460898586255056590849911 246691347879382584886274867)
  ·
    refine ⟨370037021819073877329412301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246691347879382584886274867 370037021819073877329412301)
    ·
      refine ⟨138763883182152703998529613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 370037021819073877329412301 138763883182152703998529613)
      ·
        refine ⟨52036456193307263999448605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138763883182152703998529613 52036456193307263999448605)
        ·
          refine ⟨19513671072490223999793227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52036456193307263999448605 19513671072490223999793227)
          ·
            refine ⟨29270506608735335999689841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19513671072490223999793227 29270506608735335999689841)
            ·
              refine ⟨21952879956551501999767381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29270506608735335999689841 21952879956551501999767381)
              ·
                refine ⟨128630155995418957029887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21952879956551501999767381 128630155995418957029887)
                ·
                  rfl

theorem cell23_6763671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 9].length) (baseStart_6763671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763671 prefixEnd_6763671 := by exact prefixLift 6763671
  have htrace : WordTrace (prefixWord ++ tailWord_6763671) baseStart_6763671 baseEnd_6763671 := by
    simpa [prefixWord, tailWord_6763671, baseEnd_6763671] using wordTrace_append hprefix tailTrace_6763671
  have hstable : (prefixWord ++ tailWord_6763671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763671).length < 2 ^ (prefixWord ++ tailWord_6763671).sum := by decide
  have hdescent : baseEnd_6763671 < baseStart_6763671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763693 : List Nat := [1, 5, 2, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_6763693 : Nat := 118140960795 + 6763693 * 2 ^ 59
def prefixEnd_6763693 : Nat := 4983230072969 + 3 ^ 40 * 6763693 * 2
def baseEnd_6763693 : Nat := 3473025508450710753731849

theorem tailTrace_6763693 : CollatzResearch.WordTrace tailWord_6763693 prefixEnd_6763693 3473025508450710753731849 := by
  unfold tailWord_6763693
  simp only [CollatzResearch.WordTrace]
  refine ⟨246692150285302882643575733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164461433523535255095717155 246692150285302882643575733)
  ·
    refine ⟨23127389089247145247835225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246692150285302882643575733 23127389089247145247835225)
    ·
      refine ⟨17345541816935358935876419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23127389089247145247835225 17345541816935358935876419)
      ·
        refine ⟨26018312725403038403814629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17345541816935358935876419 26018312725403038403814629)
        ·
          refine ⟨4878433636013069700715243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26018312725403038403814629 4878433636013069700715243)
          ·
            refine ⟨7317650454019604551072865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4878433636013069700715243 7317650454019604551072865)
            ·
              refine ⟨5488237840514703413304649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7317650454019604551072865 5488237840514703413304649)
              ·
                refine ⟨4116178380386027559978487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5488237840514703413304649 4116178380386027559978487)
                ·
                  refine ⟨6174267570579041339967731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116178380386027559978487 6174267570579041339967731)
                  ·
                    refine ⟨9261401355868562009951597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174267570579041339967731 9261401355868562009951597)
                    ·
                      refine ⟨3473025508450710753731849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9261401355868562009951597 3473025508450710753731849)
                      ·
                        rfl

theorem cell23_6763693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_6763693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763693 prefixEnd_6763693 := by exact prefixLift 6763693
  have htrace : WordTrace (prefixWord ++ tailWord_6763693) baseStart_6763693 baseEnd_6763693 := by
    simpa [prefixWord, tailWord_6763693, baseEnd_6763693] using wordTrace_append hprefix tailTrace_6763693
  have hstable : (prefixWord ++ tailWord_6763693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763693).length < 2 ^ (prefixWord ++ tailWord_6763693).sum := by decide
  have hdescent : baseEnd_6763693 < baseStart_6763693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763699 : List Nat := [1, 1, 1, 2, 3, 2, 6, 2, 1, 2, 2]
def baseStart_6763699 : Nat := 118140960795 + 6763699 * 2 ^ 59
def prefixEnd_6763699 : Nat := 4983230072969 + 3 ^ 40 * 6763699 * 2
def baseEnd_6763699 : Nat := 3473028589334637730256821

theorem tailTrace_6763699 : CollatzResearch.WordTrace tailWord_6763699 prefixEnd_6763699 3473028589334637730256821 := by
  unfold tailWord_6763699
  simp only [CollatzResearch.WordTrace]
  refine ⟨246692369123281145668294151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164461579415520763778862767 246692369123281145668294151)
  ·
    refine ⟨370038553684921718502441227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246692369123281145668294151 370038553684921718502441227)
    ·
      refine ⟨555057830527382577753661841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370038553684921718502441227 555057830527382577753661841)
      ·
        refine ⟨416293372895536933315246381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555057830527382577753661841 416293372895536933315246381)
        ·
          refine ⟨156110014835826349993217393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416293372895536933315246381 156110014835826349993217393)
          ·
            refine ⟨117082511126869762494913045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156110014835826349993217393 117082511126869762494913045)
            ·
              refine ⟨5488242709072020116949049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117082511126869762494913045 5488242709072020116949049)
              ·
                refine ⟨4116182031804015087711787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5488242709072020116949049 4116182031804015087711787)
                ·
                  refine ⟨6174273047706022631567681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116182031804015087711787 6174273047706022631567681)
                  ·
                    refine ⟨4630704785779516973675761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6174273047706022631567681 4630704785779516973675761)
                    ·
                      refine ⟨3473028589334637730256821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630704785779516973675761 3473028589334637730256821)
                      ·
                        rfl

theorem cell23_6763699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 1, 2, 2].length) (baseStart_6763699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763699 prefixEnd_6763699 := by exact prefixLift 6763699
  have htrace : WordTrace (prefixWord ++ tailWord_6763699) baseStart_6763699 baseEnd_6763699 := by
    simpa [prefixWord, tailWord_6763699, baseEnd_6763699] using wordTrace_append hprefix tailTrace_6763699
  have hstable : (prefixWord ++ tailWord_6763699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763699).length < 2 ^ (prefixWord ++ tailWord_6763699).sum := by decide
  have hdescent : baseEnd_6763699 < baseStart_6763699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763749 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 3]
def baseStart_6763749 : Nat := 118140960795 + 6763749 * 2 ^ 59
def prefixEnd_6763749 : Nat := 4983230072969 + 3 ^ 40 * 6763749 * 2
def baseEnd_6763749 : Nat := 3473054263367362534631591

theorem tailTrace_6763749 : CollatzResearch.WordTrace tailWord_6763749 prefixEnd_6763749 3473054263367362534631591 := by
  unfold tailWord_6763749
  simp only [CollatzResearch.WordTrace]
  refine ⟨246694192773100004207614301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164462795182066669471742867 246694192773100004207614301)
  ·
    refine ⟨92510322289912501577855363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246694192773100004207614301 92510322289912501577855363)
    ·
      refine ⟨138765483434868752366783045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92510322289912501577855363 138765483434868752366783045)
      ·
        refine ⟨26018528144037891068771821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138765483434868752366783045 26018528144037891068771821)
        ·
          refine ⟨9756948054014209150789433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26018528144037891068771821 9756948054014209150789433)
          ·
            refine ⟨7317711040510656863092075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9756948054014209150789433 7317711040510656863092075)
            ·
              refine ⟨10976566560765985294638113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7317711040510656863092075 10976566560765985294638113)
              ·
                refine ⟨8232424920574488970978585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10976566560765985294638113 8232424920574488970978585)
                ·
                  refine ⟨6174318690430866728233939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8232424920574488970978585 6174318690430866728233939)
                  ·
                    refine ⟨9261478035646300092350909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174318690430866728233939 9261478035646300092350909)
                    ·
                      refine ⟨3473054263367362534631591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9261478035646300092350909 3473054263367362534631591)
                      ·
                        rfl

theorem cell23_6763749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_6763749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763749 prefixEnd_6763749 := by exact prefixLift 6763749
  have htrace : WordTrace (prefixWord ++ tailWord_6763749) baseStart_6763749 baseEnd_6763749 := by
    simpa [prefixWord, tailWord_6763749, baseEnd_6763749] using wordTrace_append hprefix tailTrace_6763749
  have hstable : (prefixWord ++ tailWord_6763749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763749).length < 2 ^ (prefixWord ++ tailWord_6763749).sum := by decide
  have hdescent : baseEnd_6763749 < baseStart_6763749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763758 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_6763758 : Nat := 118140960795 + 6763758 * 2 ^ 59
def prefixEnd_6763758 : Nat := 4983230072969 + 3 ^ 40 * 6763758 * 2
def baseEnd_6763758 : Nat := 3473058884693252999419049

theorem tailTrace_6763758 : CollatzResearch.WordTrace tailWord_6763758 prefixEnd_6763758 3473058884693252999419049 := by
  unfold tailWord_6763758
  simp only [CollatzResearch.WordTrace]
  refine ⟨30836815128758424843086491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164463014020044932496461285 30836815128758424843086491)
  ·
    refine ⟨46255222693137637264629737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30836815128758424843086491 46255222693137637264629737)
    ·
      refine ⟨34691417019853227948472303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46255222693137637264629737 34691417019853227948472303)
      ·
        refine ⟨52037125529779841922708455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34691417019853227948472303 52037125529779841922708455)
        ·
          refine ⟨78055688294669762884062683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52037125529779841922708455 78055688294669762884062683)
          ·
            refine ⟨117083532442004644326094025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78055688294669762884062683 117083532442004644326094025)
            ·
              refine ⟨87812649331503483244570519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117083532442004644326094025 87812649331503483244570519)
              ·
                refine ⟨131718973997255224866855779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87812649331503483244570519 131718973997255224866855779)
                ·
                  refine ⟨197578460995882837300283669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131718973997255224866855779 197578460995882837300283669)
                  ·
                    refine ⟨9261490359182007998450797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 197578460995882837300283669 9261490359182007998450797)
                    ·
                      refine ⟨3473058884693252999419049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9261490359182007998450797 3473058884693252999419049)
                      ·
                        rfl

theorem cell23_6763758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_6763758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763758 prefixEnd_6763758 := by exact prefixLift 6763758
  have htrace : WordTrace (prefixWord ++ tailWord_6763758) baseStart_6763758 baseEnd_6763758 := by
    simpa [prefixWord, tailWord_6763758, baseEnd_6763758] using wordTrace_append hprefix tailTrace_6763758
  have hstable : (prefixWord ++ tailWord_6763758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763758).length < 2 ^ (prefixWord ++ tailWord_6763758).sum := by decide
  have hdescent : baseEnd_6763758 < baseStart_6763758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763801 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_6763801 : Nat := 118140960795 + 6763801 * 2 ^ 59
def prefixEnd_6763801 : Nat := 4983230072969 + 3 ^ 40 * 6763801 * 2
def baseEnd_6763801 : Nat := 3473080964361396331181351

theorem tailTrace_6763801 : CollatzResearch.WordTrace tailWord_6763801 prefixEnd_6763801 3473080964361396331181351 := by
  unfold tailWord_6763801
  simp only [CollatzResearch.WordTrace]
  refine ⟨246696089368911617088507257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164464059579274411392338171 246696089368911617088507257)
  ·
    refine ⟨185022067026683712816380443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246696089368911617088507257 185022067026683712816380443)
    ·
      refine ⟨277533100540025569224570665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185022067026683712816380443 277533100540025569224570665)
      ·
        refine ⟨208149825405019176918427999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277533100540025569224570665 208149825405019176918427999)
        ·
          refine ⟨312224738107528765377641999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208149825405019176918427999 312224738107528765377641999)
          ·
            refine ⟨468337107161293148066462999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312224738107528765377641999 468337107161293148066462999)
            ·
              refine ⟨702505660741939722099694499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468337107161293148066462999 702505660741939722099694499)
              ·
                refine ⟨1053758491112909583149541749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702505660741939722099694499 1053758491112909583149541749)
                ·
                  refine ⟨98789858541835273420269539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1053758491112909583149541749 98789858541835273420269539)
                  ·
                    refine ⟨148184787812752910130404309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98789858541835273420269539 148184787812752910130404309)
                    ·
                      refine ⟨3473080964361396331181351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 148184787812752910130404309 3473080964361396331181351)
                      ·
                        rfl

theorem cell23_6763801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_6763801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763801 prefixEnd_6763801 := by exact prefixLift 6763801
  have htrace : WordTrace (prefixWord ++ tailWord_6763801) baseStart_6763801 baseEnd_6763801 := by
    simpa [prefixWord, tailWord_6763801, baseEnd_6763801] using wordTrace_append hprefix tailTrace_6763801
  have hstable : (prefixWord ++ tailWord_6763801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763801).length < 2 ^ (prefixWord ++ tailWord_6763801).sum := by decide
  have hdescent : baseEnd_6763801 < baseStart_6763801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763812 : List Nat := [2, 3, 1, 3, 1, 1, 5, 2, 5]
def baseStart_6763812 : Nat := 118140960795 + 6763812 * 2 ^ 59
def prefixEnd_6763812 : Nat := 4983230072969 + 3 ^ 40 * 6763812 * 2
def baseEnd_6763812 : Nat := 385898512516510643127089

theorem tailTrace_6763812 : CollatzResearch.WordTrace tailWord_6763812 prefixEnd_6763812 385898512516510643127089 := by
  unfold tailWord_6763812
  simp only [CollatzResearch.WordTrace]
  refine ⟨123348245285935882983578845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164464327047914510644771793 123348245285935882983578845)
  ·
    refine ⟨46255591982225956118842067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123348245285935882983578845 46255591982225956118842067)
    ·
      refine ⟨69383387973338934178263101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46255591982225956118842067 69383387973338934178263101)
      ·
        refine ⟨26018770490002100316848663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69383387973338934178263101 26018770490002100316848663)
        ·
          refine ⟨39028155735003150475272995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26018770490002100316848663 39028155735003150475272995)
          ·
            refine ⟨58542233602504725712909493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39028155735003150475272995 58542233602504725712909493)
            ·
              refine ⟨5488334400234818035585265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58542233602504725712909493 5488334400234818035585265)
              ·
                refine ⟨4116250800176113526688949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5488334400234818035585265 4116250800176113526688949)
                ·
                  refine ⟨385898512516510643127089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4116250800176113526688949 385898512516510643127089)
                  ·
                    rfl

theorem cell23_6763812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_6763812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763812 prefixEnd_6763812 := by exact prefixLift 6763812
  have htrace : WordTrace (prefixWord ++ tailWord_6763812) baseStart_6763812 baseEnd_6763812 := by
    simpa [prefixWord, tailWord_6763812, baseEnd_6763812] using wordTrace_append hprefix tailTrace_6763812
  have hstable : (prefixWord ++ tailWord_6763812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763812).length < 2 ^ (prefixWord ++ tailWord_6763812).sum := by decide
  have hdescent : baseEnd_6763812 < baseStart_6763812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763858 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_6763858 : Nat := 118140960795 + 6763858 * 2 ^ 59
def prefixEnd_6763858 : Nat := 4983230072969 + 3 ^ 40 * 6763858 * 2
def baseEnd_6763858 : Nat := 3473110232758702608168589

theorem tailTrace_6763858 : CollatzResearch.WordTrace tailWord_6763858 prefixEnd_6763858 3473110232758702608168589 := by
  unfold tailWord_6763858
  simp only [CollatzResearch.WordTrace]
  refine ⟨61674542082426278955833057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164465445553136743882221485 61674542082426278955833057)
  ·
    refine ⟨46255906561819709216874793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61674542082426278955833057 46255906561819709216874793)
    ·
      refine ⟨34691929921364781912656095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46255906561819709216874793 34691929921364781912656095)
      ·
        refine ⟨52037894882047172868984143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34691929921364781912656095 52037894882047172868984143)
        ·
          refine ⟨78056842323070759303476215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52037894882047172868984143 78056842323070759303476215)
          ·
            refine ⟨117085263484606138955214323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78056842323070759303476215 117085263484606138955214323)
            ·
              refine ⟨175627895226909208432821485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117085263484606138955214323 175627895226909208432821485)
              ·
                refine ⟨65860460710090953162308057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175627895226909208432821485 65860460710090953162308057)
                ·
                  refine ⟨49395345532568214871731043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65860460710090953162308057 49395345532568214871731043)
                  ·
                    refine ⟨74093018298852322307596565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49395345532568214871731043 74093018298852322307596565)
                    ·
                      refine ⟨3473110232758702608168589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74093018298852322307596565 3473110232758702608168589)
                      ·
                        rfl

theorem cell23_6763858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_6763858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763858 prefixEnd_6763858 := by exact prefixLift 6763858
  have htrace : WordTrace (prefixWord ++ tailWord_6763858) baseStart_6763858 baseEnd_6763858 := by
    simpa [prefixWord, tailWord_6763858, baseEnd_6763858] using wordTrace_append hprefix tailTrace_6763858
  have hstable : (prefixWord ++ tailWord_6763858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763858).length < 2 ^ (prefixWord ++ tailWord_6763858).sum := by decide
  have hdescent : baseEnd_6763858 < baseStart_6763858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763865 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 3]
def baseStart_6763865 : Nat := 118140960795 + 6763865 * 2 ^ 59
def prefixEnd_6763865 : Nat := 4983230072969 + 3 ^ 40 * 6763865 * 2
def baseEnd_6763865 : Nat := 3473113827123284080781057

theorem tailTrace_6763865 : CollatzResearch.WordTrace tailWord_6763865 prefixEnd_6763865 3473113827123284080781057 := by
  unfold tailWord_6763865
  simp only [CollatzResearch.WordTrace]
  refine ⟨246698423640679756018837049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164465615760453170679224699 246698423640679756018837049)
  ·
    refine ⟨185023817730509817014127787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246698423640679756018837049 185023817730509817014127787)
    ·
      refine ⟨277535726595764725521191681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185023817730509817014127787 277535726595764725521191681)
      ·
        refine ⟨208151794946823544140893761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277535726595764725521191681 208151794946823544140893761)
        ·
          refine ⟨156113846210117658105670321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208151794946823544140893761 156113846210117658105670321)
          ·
            refine ⟨117085384657588243579252741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156113846210117658105670321 117085384657588243579252741)
            ·
              refine ⟨21953509623297795671109889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117085384657588243579252741 21953509623297795671109889)
              ·
                refine ⟨16465132217473346753332417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21953509623297795671109889 16465132217473346753332417)
                ·
                  refine ⟨12348849163105010064999313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16465132217473346753332417 12348849163105010064999313)
                  ·
                    refine ⟨9261636872328757548749485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12348849163105010064999313 9261636872328757548749485)
                    ·
                      refine ⟨3473113827123284080781057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9261636872328757548749485 3473113827123284080781057)
                      ·
                        rfl

theorem cell23_6763865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_6763865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763865 prefixEnd_6763865 := by exact prefixLift 6763865
  have htrace : WordTrace (prefixWord ++ tailWord_6763865) baseStart_6763865 baseEnd_6763865 := by
    simpa [prefixWord, tailWord_6763865, baseEnd_6763865] using wordTrace_append hprefix tailTrace_6763865
  have hstable : (prefixWord ++ tailWord_6763865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763865).length < 2 ^ (prefixWord ++ tailWord_6763865).sum := by decide
  have hdescent : baseEnd_6763865 < baseStart_6763865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763885 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 6]
def baseStart_6763885 : Nat := 118140960795 + 6763885 * 2 ^ 59
def prefixEnd_6763885 : Nat := 4983230072969 + 3 ^ 40 * 6763885 * 2
def baseEnd_6763885 : Nat := 385902677415152666947885

theorem tailTrace_6763885 : CollatzResearch.WordTrace tailWord_6763885 prefixEnd_6763885 385902677415152666947885 := by
  unfold tailWord_6763885
  simp only [CollatzResearch.WordTrace]
  refine ⟨246699153100607299434565109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164466102067071532956376739 246699153100607299434565109)
  ·
    refine ⟨23128045603181934321990479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246699153100607299434565109 23128045603181934321990479)
    ·
      refine ⟨34692068404772901482985719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23128045603181934321990479 34692068404772901482985719)
      ·
        refine ⟨52038102607159352224478579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34692068404772901482985719 52038102607159352224478579)
        ·
          refine ⟨78057153910739028336717869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52038102607159352224478579 78057153910739028336717869)
          ·
            refine ⟨29271432716527135626269201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78057153910739028336717869 29271432716527135626269201)
            ·
              refine ⟨21953574537395351719701901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29271432716527135626269201 21953574537395351719701901)
              ·
                refine ⟨8232590451523256894888213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21953574537395351719701901 8232590451523256894888213)
                ·
                  refine ⟨385902677415152666947885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8232590451523256894888213 385902677415152666947885)
                  ·
                    rfl

theorem cell23_6763885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_6763885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763885 prefixEnd_6763885 := by exact prefixLift 6763885
  have htrace : WordTrace (prefixWord ++ tailWord_6763885) baseStart_6763885 baseEnd_6763885 := by
    simpa [prefixWord, tailWord_6763885, baseEnd_6763885] using wordTrace_append hprefix tailTrace_6763885
  have hstable : (prefixWord ++ tailWord_6763885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763885).length < 2 ^ (prefixWord ++ tailWord_6763885).sum := by decide
  have hdescent : baseEnd_6763885 < baseStart_6763885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763906 : List Nat := [3, 4, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6763906 : Nat := 118140960795 + 6763906 * 2 ^ 59
def prefixEnd_6763906 : Nat := 4983230072969 + 3 ^ 40 * 6763906 * 2
def baseEnd_6763906 : Nat := 1157711626610039473456123

theorem tailTrace_6763906 : CollatzResearch.WordTrace tailWord_6763906 prefixEnd_6763906 1157711626610039473456123 := by
  unfold tailWord_6763906
  simp only [CollatzResearch.WordTrace]
  refine ⟨61674979758382805005269893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 164466612689020813347386381 61674979758382805005269893)
  ·
    refine ⟨11564058704696775938488105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61674979758382805005269893 11564058704696775938488105)
    ·
      refine ⟨8673044028522581953866079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11564058704696775938488105 8673044028522581953866079)
      ·
        refine ⟨13009566042783872930799119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8673044028522581953866079 13009566042783872930799119)
        ·
          refine ⟨19514349064175809396198679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13009566042783872930799119 19514349064175809396198679)
          ·
            refine ⟨29271523596263714094298019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19514349064175809396198679 29271523596263714094298019)
            ·
              refine ⟨43907285394395571141447029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29271523596263714094298019 43907285394395571141447029)
              ·
                refine ⟨4116308005724584794510659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43907285394395571141447029 4116308005724584794510659)
                ·
                  refine ⟨6174462008586877191765989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116308005724584794510659 6174462008586877191765989)
                  ·
                    refine ⟨1157711626610039473456123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6174462008586877191765989 1157711626610039473456123)
                    ·
                      rfl

theorem cell23_6763906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6763906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763906 prefixEnd_6763906 := by exact prefixLift 6763906
  have htrace : WordTrace (prefixWord ++ tailWord_6763906) baseStart_6763906 baseEnd_6763906 := by
    simpa [prefixWord, tailWord_6763906, baseEnd_6763906] using wordTrace_append hprefix tailTrace_6763906
  have hstable : (prefixWord ++ tailWord_6763906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763906).length < 2 ^ (prefixWord ++ tailWord_6763906).sum := by decide
  have hdescent : baseEnd_6763906 < baseStart_6763906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763915 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 1, 5]
def baseStart_6763915 : Nat := 118140960795 + 6763915 * 2 ^ 59
def prefixEnd_6763915 : Nat := 4983230072969 + 3 ^ 40 * 6763915 * 2
def baseEnd_6763915 : Nat := 1157713167052002961718609

theorem tailTrace_6763915 : CollatzResearch.WordTrace tailWord_6763915 prefixEnd_6763915 1157713167052002961718609 := by
  unfold tailWord_6763915
  simp only [CollatzResearch.WordTrace]
  refine ⟨246700247290498614558157199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164466831526999076372104799 246700247290498614558157199)
  ·
    refine ⟨370050370935747921837235799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246700247290498614558157199 370050370935747921837235799)
    ·
      refine ⟨555075556403621882755853699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370050370935747921837235799 555075556403621882755853699)
      ·
        refine ⟨832613334605432824133780549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555075556403621882755853699 832613334605432824133780549)
        ·
          refine ⟨156115000238518654525083853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 832613334605432824133780549 156115000238518654525083853)
          ·
            refine ⟨58543125089444495446906445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156115000238518654525083853 58543125089444495446906445)
            ·
              refine ⟨21953671908541685792589917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58543125089444495446906445 21953671908541685792589917)
              ·
                refine ⟨8232626965703132172221219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21953671908541685792589917 8232626965703132172221219)
                ·
                  refine ⟨12348940448554698258331829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8232626965703132172221219 12348940448554698258331829)
                  ·
                    refine ⟨1157713167052002961718609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12348940448554698258331829 1157713167052002961718609)
                    ·
                      rfl

theorem cell23_6763915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 5].length) (baseStart_6763915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763915 prefixEnd_6763915 := by exact prefixLift 6763915
  have htrace : WordTrace (prefixWord ++ tailWord_6763915) baseStart_6763915 baseEnd_6763915 := by
    simpa [prefixWord, tailWord_6763915, baseEnd_6763915] using wordTrace_append hprefix tailTrace_6763915
  have hstable : (prefixWord ++ tailWord_6763915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763915).length < 2 ^ (prefixWord ++ tailWord_6763915).sum := by decide
  have hdescent : baseEnd_6763915 < baseStart_6763915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763929 : List Nat := [1, 2, 1, 2, 1, 5, 2, 4, 1, 1, 3]
def baseStart_6763929 : Nat := 118140960795 + 6763929 * 2 ^ 59
def prefixEnd_6763929 : Nat := 4983230072969 + 3 ^ 40 * 6763929 * 2
def baseEnd_6763929 : Nat := 3473146689885171830380763

theorem tailTrace_6763929 : CollatzResearch.WordTrace tailWord_6763929 prefixEnd_6763929 3473146689885171830380763 := by
  unfold tailWord_6763929
  simp only [CollatzResearch.WordTrace]
  refine ⟨246700757912447894949166841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164467171941631929966111227 246700757912447894949166841)
  ·
    refine ⟨185025568434335921211875131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246700757912447894949166841 185025568434335921211875131)
    ·
      refine ⟨277538352651503881817812697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185025568434335921211875131 277538352651503881817812697)
      ·
        refine ⟨208153764488627911363359523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277538352651503881817812697 208153764488627911363359523)
        ·
          refine ⟨312230646732941867045039285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208153764488627911363359523 312230646732941867045039285)
          ·
            refine ⟨29271623131213300035472433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 312230646732941867045039285 29271623131213300035472433)
            ·
              refine ⟨21953717348409975026604325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29271623131213300035472433 21953717348409975026604325)
              ·
                refine ⟨4116322002826870317488311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21953717348409975026604325 4116322002826870317488311)
                ·
                  refine ⟨6174483004240305476232467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116322002826870317488311 6174483004240305476232467)
                  ·
                    refine ⟨9261724506360458214348701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174483004240305476232467 9261724506360458214348701)
                    ·
                      refine ⟨3473146689885171830380763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9261724506360458214348701 3473146689885171830380763)
                      ·
                        rfl

theorem cell23_6763929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 1, 1, 3].length) (baseStart_6763929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763929 prefixEnd_6763929 := by exact prefixLift 6763929
  have htrace : WordTrace (prefixWord ++ tailWord_6763929) baseStart_6763929 baseEnd_6763929 := by
    simpa [prefixWord, tailWord_6763929, baseEnd_6763929] using wordTrace_append hprefix tailTrace_6763929
  have hstable : (prefixWord ++ tailWord_6763929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763929).length < 2 ^ (prefixWord ++ tailWord_6763929).sum := by decide
  have hdescent : baseEnd_6763929 < baseStart_6763929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763949 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_6763949 : Nat := 118140960795 + 6763949 * 2 ^ 59
def prefixEnd_6763949 : Nat := 4983230072969 + 3 ^ 40 * 6763949 * 2
def baseEnd_6763949 : Nat := 1157718986499420584043557

theorem tailTrace_6763949 : CollatzResearch.WordTrace tailWord_6763949 prefixEnd_6763949 1157718986499420584043557 := by
  unfold tailWord_6763949
  simp only [CollatzResearch.WordTrace]
  refine ⟨246701487372375438364894901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164467658248250292243263267 246701487372375438364894901)
  ·
    refine ⟨23128264441160197346708897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 246701487372375438364894901 23128264441160197346708897)
    ·
      refine ⟨17346198330870148010031673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23128264441160197346708897 17346198330870148010031673)
      ·
        refine ⟨13009648748152611007523755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17346198330870148010031673 13009648748152611007523755)
        ·
          refine ⟨19514473122228916511285633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13009648748152611007523755 19514473122228916511285633)
          ·
            refine ⟨14635854841671687383464225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19514473122228916511285633 14635854841671687383464225)
            ·
              refine ⟨10976891131253765537598169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14635854841671687383464225 10976891131253765537598169)
              ·
                refine ⟨8232668348440324153198627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10976891131253765537598169 8232668348440324153198627)
                ·
                  refine ⟨12349002522660486229797941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8232668348440324153198627 12349002522660486229797941)
                  ·
                    refine ⟨1157718986499420584043557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12349002522660486229797941 1157718986499420584043557)
                    ·
                      rfl

theorem cell23_6763949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_6763949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763949 prefixEnd_6763949 := by exact prefixLift 6763949
  have htrace : WordTrace (prefixWord ++ tailWord_6763949) baseStart_6763949 baseEnd_6763949 := by
    simpa [prefixWord, tailWord_6763949, baseEnd_6763949] using wordTrace_append hprefix tailTrace_6763949
  have hstable : (prefixWord ++ tailWord_6763949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763949).length < 2 ^ (prefixWord ++ tailWord_6763949).sum := by decide
  have hdescent : baseEnd_6763949 < baseStart_6763949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763952 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 5, 2, 2]
def baseStart_6763952 : Nat := 118140960795 + 6763952 * 2 ^ 59
def prefixEnd_6763952 : Nat := 4983230072969 + 3 ^ 40 * 6763952 * 2
def baseEnd_6763952 : Nat := 3473158499940225240393157

theorem tailTrace_6763952 : CollatzResearch.WordTrace tailWord_6763952 prefixEnd_6763952 3473158499940225240393157 := by
  unfold tailWord_6763952
  simp only [CollatzResearch.WordTrace]
  refine ⟨123350798395682284938627055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164467731194243046584836073 123350798395682284938627055)
  ·
    refine ⟨185026197593523427407940583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123350798395682284938627055 185026197593523427407940583)
    ·
      refine ⟨277539296390285141111910875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185026197593523427407940583 277539296390285141111910875)
      ·
        refine ⟨416308944585427711667866313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277539296390285141111910875 416308944585427711667866313)
        ·
          refine ⟨312231708439070783750899735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416308944585427711667866313 312231708439070783750899735)
          ·
            refine ⟨468347562658606175626349603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312231708439070783750899735 468347562658606175626349603)
            ·
              refine ⟨702521343987909263439524405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468347562658606175626349603 702521343987909263439524405)
              ·
                refine ⟨65861375998866493447455413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 702521343987909263439524405 65861375998866493447455413)
                ·
                  refine ⟨6174503999893733760698945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65861375998866493447455413 6174503999893733760698945)
                  ·
                    refine ⟨4630877999920300320524209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6174503999893733760698945 4630877999920300320524209)
                    ·
                      refine ⟨3473158499940225240393157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4630877999920300320524209 3473158499940225240393157)
                      ·
                        rfl

theorem cell23_6763952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 2, 2].length) (baseStart_6763952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763952 prefixEnd_6763952 := by exact prefixLift 6763952
  have htrace : WordTrace (prefixWord ++ tailWord_6763952) baseStart_6763952 baseEnd_6763952 := by
    simpa [prefixWord, tailWord_6763952, baseEnd_6763952] using wordTrace_append hprefix tailTrace_6763952
  have hstable : (prefixWord ++ tailWord_6763952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763952).length < 2 ^ (prefixWord ++ tailWord_6763952).sum := by decide
  have hdescent : baseEnd_6763952 < baseStart_6763952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763955 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 3]
def baseStart_6763955 : Nat := 118140960795 + 6763955 * 2 ^ 59
def prefixEnd_6763955 : Nat := 4983230072969 + 3 ^ 40 * 6763955 * 2
def baseEnd_6763955 : Nat := 3473160040382188728655643

theorem tailTrace_6763955 : CollatzResearch.WordTrace tailWord_6763955 prefixEnd_6763955 3473160040382188728655643 := by
  unfold tailWord_6763955
  simp only [CollatzResearch.WordTrace]
  refine ⟨246701706210353701389613319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164467804140235800926408879 246701706210353701389613319)
  ·
    refine ⟨370052559315530552084419979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246701706210353701389613319 370052559315530552084419979)
    ·
      refine ⟨555078838973295828126629969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370052559315530552084419979 555078838973295828126629969)
      ·
        refine ⟨416309129229971871094972477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555078838973295828126629969 416309129229971871094972477)
        ·
          refine ⟨156115923461239451660614679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416309129229971871094972477 156115923461239451660614679)
          ·
            refine ⟨234173885191859177490922019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156115923461239451660614679 234173885191859177490922019)
            ·
              refine ⟨351260827787788766236383029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234173885191859177490922019 351260827787788766236383029)
              ·
                refine ⟨32930702605105196834660909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351260827787788766236383029 32930702605105196834660909)
                ·
                  refine ⟨12349013476914448812997841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32930702605105196834660909 12349013476914448812997841)
                  ·
                    refine ⟨9261760107685836609748381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12349013476914448812997841 9261760107685836609748381)
                    ·
                      refine ⟨3473160040382188728655643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9261760107685836609748381 3473160040382188728655643)
                      ·
                        rfl

theorem cell23_6763955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_6763955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763955 prefixEnd_6763955 := by exact prefixLift 6763955
  have htrace : WordTrace (prefixWord ++ tailWord_6763955) baseStart_6763955 baseEnd_6763955 := by
    simpa [prefixWord, tailWord_6763955, baseEnd_6763955] using wordTrace_append hprefix tailTrace_6763955
  have hstable : (prefixWord ++ tailWord_6763955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763955).length < 2 ^ (prefixWord ++ tailWord_6763955).sum := by decide
  have hdescent : baseEnd_6763955 < baseStart_6763955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763965 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_6763965 : Nat := 118140960795 + 6763965 * 2 ^ 59
def prefixEnd_6763965 : Nat := 4983230072969 + 3 ^ 40 * 6763965 * 2
def baseEnd_6763965 : Nat := 3473165175188733689530597

theorem tailTrace_6763965 : CollatzResearch.WordTrace tailWord_6763965 prefixEnd_6763965 3473165175188733689530597 := by
  unfold tailWord_6763965
  simp only [CollatzResearch.WordTrace]
  refine ⟨246702070940317473097477349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164468047293544982064984899 246702070940317473097477349)
  ·
    refine ⟨46256638301309526205777003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 246702070940317473097477349 46256638301309526205777003)
    ·
      refine ⟨69384957451964289308665505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46256638301309526205777003 69384957451964289308665505)
      ·
        refine ⟨52038718088973216981499129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69384957451964289308665505 52038718088973216981499129)
        ·
          refine ⟨39029038566729912736124347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52038718088973216981499129 39029038566729912736124347)
          ·
            refine ⟨58543557850094869104186521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39029038566729912736124347 58543557850094869104186521)
            ·
              refine ⟨43907668387571151828139891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58543557850094869104186521 43907668387571151828139891)
              ·
                refine ⟨65861502581356727742209837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43907668387571151828139891 65861502581356727742209837)
                ·
                  refine ⟨24698063468008772903328689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65861502581356727742209837 24698063468008772903328689)
                  ·
                    refine ⟨18523547601006579677496517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24698063468008772903328689 18523547601006579677496517)
                    ·
                      refine ⟨3473165175188733689530597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18523547601006579677496517 3473165175188733689530597)
                      ·
                        rfl

theorem cell23_6763965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_6763965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763965 prefixEnd_6763965 := by exact prefixLift 6763965
  have htrace : WordTrace (prefixWord ++ tailWord_6763965) baseStart_6763965 baseEnd_6763965 := by
    simpa [prefixWord, tailWord_6763965, baseEnd_6763965] using wordTrace_append hprefix tailTrace_6763965
  have hstable : (prefixWord ++ tailWord_6763965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763965).length < 2 ^ (prefixWord ++ tailWord_6763965).sum := by decide
  have hdescent : baseEnd_6763965 < baseStart_6763965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6763972 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6763972 : Nat := 118140960795 + 6763972 * 2 ^ 59
def prefixEnd_6763972 : Nat := 4983230072969 + 3 ^ 40 * 6763972 * 2
def baseEnd_6763972 : Nat := 3473168769553315162143065

theorem tailTrace_6763972 : CollatzResearch.WordTrace tailWord_6763972 prefixEnd_6763972 3473168769553315162143065 := by
  unfold tailWord_6763972
  simp only [CollatzResearch.WordTrace]
  refine ⟨123351163125646056646491085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164468217500861408861988113 123351163125646056646491085)
  ·
    refine ⟨46256686172117271242434157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123351163125646056646491085 46256686172117271242434157)
    ·
      refine ⟨17346257314543976715912809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46256686172117271242434157 17346257314543976715912809)
      ·
        refine ⟨13009692985907982536934607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17346257314543976715912809 13009692985907982536934607)
        ·
          refine ⟨19514539478861973805401911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13009692985907982536934607 19514539478861973805401911)
          ·
            refine ⟨29271809218292960708102867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19514539478861973805401911 29271809218292960708102867)
            ·
              refine ⟨43907713827439441062154301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29271809218292960708102867 43907713827439441062154301)
              ·
                refine ⟨16465392685289790398307863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43907713827439441062154301 16465392685289790398307863)
                ·
                  refine ⟨24698089027934685597461795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16465392685289790398307863 24698089027934685597461795)
                  ·
                    refine ⟨37047133541902028396192693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24698089027934685597461795 37047133541902028396192693)
                    ·
                      refine ⟨3473168769553315162143065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37047133541902028396192693 3473168769553315162143065)
                      ·
                        rfl

theorem cell23_6763972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6763972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6763972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6763972 prefixEnd_6763972 := by exact prefixLift 6763972
  have htrace : WordTrace (prefixWord ++ tailWord_6763972) baseStart_6763972 baseEnd_6763972 := by
    simpa [prefixWord, tailWord_6763972, baseEnd_6763972] using wordTrace_append hprefix tailTrace_6763972
  have hstable : (prefixWord ++ tailWord_6763972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6763972).length < 2 ^ (prefixWord ++ tailWord_6763972).sum := by decide
  have hdescent : baseEnd_6763972 < baseStart_6763972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6763972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764065 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 9]
def baseStart_6764065 : Nat := 118140960795 + 6764065 * 2 ^ 59
def prefixEnd_6764065 : Nat := 4983230072969 + 3 ^ 40 * 6764065 * 2
def baseEnd_6764065 : Nat := 385912947028242588697793

theorem tailTrace_6764065 : CollatzResearch.WordTrace tailWord_6764065 prefixEnd_6764065 385912947028242588697793 := by
  unfold tailWord_6764065
  simp only [CollatzResearch.WordTrace]
  refine ⟨246705718239955190176117649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164470478826636793450745099 246705718239955190176117649)
  ·
    refine ⟨185029288679966392632088237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246705718239955190176117649 185029288679966392632088237)
    ·
      refine ⟨69385983254987397237033089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185029288679966392632088237 69385983254987397237033089)
      ·
        refine ⟨52039487441240547927774817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69385983254987397237033089 52039487441240547927774817)
        ·
          refine ⟨39029615580930410945831113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52039487441240547927774817 39029615580930410945831113)
          ·
            refine ⟨29272211685697808209373335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39029615580930410945831113 29272211685697808209373335)
            ·
              refine ⟨43908317528546712314060003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29272211685697808209373335 43908317528546712314060003)
              ·
                refine ⟨65862476292820068471090005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43908317528546712314060003 65862476292820068471090005)
                ·
                  refine ⟨385912947028242588697793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65862476292820068471090005 385912947028242588697793)
                  ·
                    rfl

theorem cell23_6764065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 9].length) (baseStart_6764065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764065 prefixEnd_6764065 := by exact prefixLift 6764065
  have htrace : WordTrace (prefixWord ++ tailWord_6764065) baseStart_6764065 baseEnd_6764065 := by
    simpa [prefixWord, tailWord_6764065, baseEnd_6764065] using wordTrace_append hprefix tailTrace_6764065
  have hstable : (prefixWord ++ tailWord_6764065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764065).length < 2 ^ (prefixWord ++ tailWord_6764065).sum := by decide
  have hdescent : baseEnd_6764065 < baseStart_6764065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764105 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_6764105 : Nat := 118140960795 + 6764105 * 2 ^ 59
def prefixEnd_6764105 : Nat := 4983230072969 + 3 ^ 40 * 6764105 * 2
def baseEnd_6764105 : Nat := 3473237062480363141779953

theorem tailTrace_6764105 : CollatzResearch.WordTrace tailWord_6764105 prefixEnd_6764105 3473237062480363141779953 := by
  unfold tailWord_6764105
  simp only [CollatzResearch.WordTrace]
  refine ⟨246707177159810277007573769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164471451439873518005049179 246707177159810277007573769)
  ·
    refine ⟨185030382869857707755680327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 246707177159810277007573769 185030382869857707755680327)
    ·
      refine ⟨277545574304786561633520491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185030382869857707755680327 277545574304786561633520491)
      ·
        refine ⟨416318361457179842450280737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277545574304786561633520491 416318361457179842450280737)
        ·
          refine ⟨312238771092884881837710553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416318361457179842450280737 312238771092884881837710553)
          ·
            refine ⟨234179078319663661378282915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312238771092884881837710553 234179078319663661378282915)
            ·
              refine ⟨351268617479495492067424373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234179078319663661378282915 351268617479495492067424373)
              ·
                refine ⟨32931432888702702381321035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351268617479495492067424373 32931432888702702381321035)
                ·
                  refine ⟨49397149333054053571981553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32931432888702702381321035 49397149333054053571981553)
                  ·
                    refine ⟨37047861999790540178986165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49397149333054053571981553 37047861999790540178986165)
                    ·
                      refine ⟨3473237062480363141779953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37047861999790540178986165 3473237062480363141779953)
                      ·
                        rfl

theorem cell23_6764105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_6764105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764105 prefixEnd_6764105 := by exact prefixLift 6764105
  have htrace : WordTrace (prefixWord ++ tailWord_6764105) baseStart_6764105 baseEnd_6764105 := by
    simpa [prefixWord, tailWord_6764105, baseEnd_6764105] using wordTrace_append hprefix tailTrace_6764105
  have hstable : (prefixWord ++ tailWord_6764105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764105).length < 2 ^ (prefixWord ++ tailWord_6764105).sum := by decide
  have hdescent : baseEnd_6764105 < baseStart_6764105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6764132 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_6764132 : Nat := 118140960795 + 6764132 * 2 ^ 59
def prefixEnd_6764132 : Nat := 4983230072969 + 3 ^ 40 * 6764132 * 2
def baseEnd_6764132 : Nat := 3473250926458034536142329

theorem tailTrace_6764132 : CollatzResearch.WordTrace tailWord_6764132 prefixEnd_6764132 3473250926458034536142329 := by
  unfold tailWord_6764132
  simp only [CollatzResearch.WordTrace]
  refine ⟨123354080965356230309403325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164472107953808307079204433 123354080965356230309403325)
  ·
    refine ⟨46257780362008586366026247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123354080965356230309403325 46257780362008586366026247)
    ·
      refine ⟨69386670543012879549039371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46257780362008586366026247 69386670543012879549039371)
      ·
        refine ⟨104080005814519319323559057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69386670543012879549039371 104080005814519319323559057)
        ·
          refine ⟨78060004360889489492669293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104080005814519319323559057 78060004360889489492669293)
          ·
            refine ⟨29272501635333558559750985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78060004360889489492669293 29272501635333558559750985)
            ·
              refine ⟨21954376226500168919813239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29272501635333558559750985 21954376226500168919813239)
              ·
                refine ⟨32931564339750253379719859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21954376226500168919813239 32931564339750253379719859)
                ·
                  refine ⟨49397346509625380069579789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32931564339750253379719859 49397346509625380069579789)
                  ·
                    refine ⟨18524004941109517526092421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49397346509625380069579789 18524004941109517526092421)
                    ·
                      refine ⟨3473250926458034536142329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18524004941109517526092421 3473250926458034536142329)
                      ·
                        rfl

theorem cell23_6764132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_6764132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6764132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6764132 prefixEnd_6764132 := by exact prefixLift 6764132
  have htrace : WordTrace (prefixWord ++ tailWord_6764132) baseStart_6764132 baseEnd_6764132 := by
    simpa [prefixWord, tailWord_6764132, baseEnd_6764132] using wordTrace_append hprefix tailTrace_6764132
  have hstable : (prefixWord ++ tailWord_6764132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6764132).length < 2 ^ (prefixWord ++ tailWord_6764132).sum := by decide
  have hdescent : baseEnd_6764132 < baseStart_6764132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6764132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
