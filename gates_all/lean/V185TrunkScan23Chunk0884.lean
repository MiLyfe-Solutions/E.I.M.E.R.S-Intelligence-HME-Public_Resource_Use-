import V185TrunkScan23Chunk0883

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5231748 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_5231748 : Nat := 118140960795 + 5231748 * 2 ^ 59
def prefixEnd_5231748 : Nat := 4983230072969 + 3 ^ 40 * 5231748 * 2
def baseEnd_5231748 : Nat := 2686401387198701995589635

theorem tailTrace_5231748 : CollatzResearch.WordTrace tailWord_5231748 prefixEnd_5231748 2686401387198701995589635 := by
  unfold tailWord_5231748
  simp only [CollatzResearch.WordTrace]
  refine ⟨95408762925138991133715949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127211683900185321511621265 95408762925138991133715949)
  ·
    refine ⟨35778286096927121675143481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95408762925138991133715949 35778286096927121675143481)
    ·
      refine ⟨26833714572695341256357611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35778286096927121675143481 26833714572695341256357611)
      ·
        refine ⟨40250571859043011884536417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26833714572695341256357611 40250571859043011884536417)
        ·
          refine ⟨30187928894282258913402313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40250571859043011884536417 30187928894282258913402313)
          ·
            refine ⟨22640946670711694185051735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30187928894282258913402313 22640946670711694185051735)
            ·
              refine ⟨33961420006067541277577603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22640946670711694185051735 33961420006067541277577603)
              ·
                refine ⟨50942130009101311916366405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33961420006067541277577603 50942130009101311916366405)
                ·
                  refine ⟨9551649376706495984318701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50942130009101311916366405 9551649376706495984318701)
                  ·
                    refine ⟨3581868516264935994119513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9551649376706495984318701 3581868516264935994119513)
                    ·
                      refine ⟨2686401387198701995589635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3581868516264935994119513 2686401387198701995589635)
                      ·
                        rfl

theorem cell23_5231748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_5231748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231748 prefixEnd_5231748 := by exact prefixLift 5231748
  have htrace : WordTrace (prefixWord ++ tailWord_5231748) baseStart_5231748 baseEnd_5231748 := by
    simpa [prefixWord, tailWord_5231748, baseEnd_5231748] using wordTrace_append hprefix tailTrace_5231748
  have hstable : (prefixWord ++ tailWord_5231748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231748).length < 2 ^ (prefixWord ++ tailWord_5231748).sum := by decide
  have hdescent : baseEnd_5231748 < baseStart_5231748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231775 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 1, 5]
def baseStart_5231775 : Nat := 118140960795 + 5231775 * 2 ^ 59
def prefixEnd_5231775 : Nat := 4983230072969 + 3 ^ 40 * 5231775 * 2
def baseEnd_5231775 : Nat := 895471750392124463317337

theorem tailTrace_5231775 : CollatzResearch.WordTrace tailWord_5231775 prefixEnd_5231775 895471750392124463317337 := by
  unfold tailWord_5231775
  simp only [CollatzResearch.WordTrace]
  refine ⟨190818510621180165878664779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127212340414120110585776519 190818510621180165878664779)
  ·
    refine ⟨286227765931770248817997169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190818510621180165878664779 286227765931770248817997169)
    ·
      refine ⟨214670824448827686613497877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286227765931770248817997169 214670824448827686613497877)
      ·
        refine ⟨10062694896038797810007713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 214670824448827686613497877 10062694896038797810007713)
        ·
          refine ⟨7547021172029098357505785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10062694896038797810007713 7547021172029098357505785)
          ·
            refine ⟨5660265879021823768129339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7547021172029098357505785 5660265879021823768129339)
            ·
              refine ⟨8490398818532735652194009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5660265879021823768129339 8490398818532735652194009)
              ·
                refine ⟨6367799113899551739145507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8490398818532735652194009 6367799113899551739145507)
                ·
                  refine ⟨9551698670849327608718261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6367799113899551739145507 9551698670849327608718261)
                  ·
                    refine ⟨895471750392124463317337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9551698670849327608718261 895471750392124463317337)
                    ·
                      rfl

theorem cell23_5231775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 5].length) (baseStart_5231775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231775 prefixEnd_5231775 := by exact prefixLift 5231775
  have htrace : WordTrace (prefixWord ++ tailWord_5231775) baseStart_5231775 baseEnd_5231775 := by
    simpa [prefixWord, tailWord_5231775, baseEnd_5231775] using wordTrace_append hprefix tailTrace_5231775
  have hstable : (prefixWord ++ tailWord_5231775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231775).length < 2 ^ (prefixWord ++ tailWord_5231775).sum := by decide
  have hdescent : baseEnd_5231775 < baseStart_5231775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231881 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 4]
def baseStart_5231881 : Nat := 118140960795 + 5231881 * 2 ^ 59
def prefixEnd_5231881 : Nat := 4983230072969 + 3 ^ 40 * 5231881 * 2
def baseEnd_5231881 : Nat := 2686469680125749975226523

theorem tailTrace_5231881 : CollatzResearch.WordTrace tailWord_5231881 prefixEnd_5231881 2686469680125749975226523 := by
  unfold tailWord_5231881
  simp only [CollatzResearch.WordTrace]
  refine ⟨190822376758796145982023497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127214917839197430654682331 190822376758796145982023497)
  ·
    refine ⟨143116782569097109486517623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190822376758796145982023497 143116782569097109486517623)
    ·
      refine ⟨214675173853645664229776435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143116782569097109486517623 214675173853645664229776435)
      ·
        refine ⟨322012760780468496344664653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214675173853645664229776435 322012760780468496344664653)
        ·
          refine ⟨120754785292675686129249245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322012760780468496344664653 120754785292675686129249245)
          ·
            refine ⟨45283044484753382298468467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120754785292675686129249245 45283044484753382298468467)
            ·
              refine ⟨67924566727130073447702701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45283044484753382298468467 67924566727130073447702701)
              ·
                refine ⟨25471712522673777542888513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67924566727130073447702701 25471712522673777542888513)
                ·
                  refine ⟨19103784392005333157166385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25471712522673777542888513 19103784392005333157166385)
                  ·
                    refine ⟨14327838294003999867874789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19103784392005333157166385 14327838294003999867874789)
                    ·
                      refine ⟨2686469680125749975226523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14327838294003999867874789 2686469680125749975226523)
                      ·
                        rfl

theorem cell23_5231881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_5231881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231881 prefixEnd_5231881 := by exact prefixLift 5231881
  have htrace : WordTrace (prefixWord ++ tailWord_5231881) baseStart_5231881 baseEnd_5231881 := by
    simpa [prefixWord, tailWord_5231881, baseEnd_5231881] using wordTrace_append hprefix tailTrace_5231881
  have hstable : (prefixWord ++ tailWord_5231881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231881).length < 2 ^ (prefixWord ++ tailWord_5231881).sum := by decide
  have hdescent : baseEnd_5231881 < baseStart_5231881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231928 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 2, 5, 2]
def baseStart_5231928 : Nat := 118140960795 + 5231928 * 2 ^ 59
def prefixEnd_5231928 : Nat := 4983230072969 + 3 ^ 40 * 5231928 * 2
def baseEnd_5231928 : Nat := 2686493813716511291338807

theorem tailTrace_5231928 : CollatzResearch.WordTrace tailWord_5231928 prefixEnd_5231928 2686493813716511291338807 := by
  unfold tailWord_5231928
  simp only [CollatzResearch.WordTrace]
  refine ⟨95412045494812936504492219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127216060659750582005989625 95412045494812936504492219)
  ·
    refine ⟨143118068242219404756738329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95412045494812936504492219 143118068242219404756738329)
    ·
      refine ⟨107338551181664553567553747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143118068242219404756738329 107338551181664553567553747)
      ·
        refine ⟨161007826772496830351330621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107338551181664553567553747 161007826772496830351330621)
        ·
          refine ⟨60377935039686311381748983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161007826772496830351330621 60377935039686311381748983)
          ·
            refine ⟨90566902559529467072623475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60377935039686311381748983 90566902559529467072623475)
            ·
              refine ⟨135850353839294200608935213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90566902559529467072623475 135850353839294200608935213)
              ·
                refine ⟨50943882689735325228350705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135850353839294200608935213 50943882689735325228350705)
                ·
                  refine ⟨38207912017301493921263029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50943882689735325228350705 38207912017301493921263029)
                  ·
                    refine ⟨3581991751622015055118409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38207912017301493921263029 3581991751622015055118409)
                    ·
                      refine ⟨2686493813716511291338807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3581991751622015055118409 2686493813716511291338807)
                      ·
                        rfl

theorem cell23_5231928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_5231928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231928 prefixEnd_5231928 := by exact prefixLift 5231928
  have htrace : WordTrace (prefixWord ++ tailWord_5231928) baseStart_5231928 baseEnd_5231928 := by
    simpa [prefixWord, tailWord_5231928, baseEnd_5231928] using wordTrace_append hprefix tailTrace_5231928
  have hstable : (prefixWord ++ tailWord_5231928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231928).length < 2 ^ (prefixWord ++ tailWord_5231928).sum := by decide
  have hdescent : baseEnd_5231928 < baseStart_5231928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5231941 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_5231941 : Nat := 118140960795 + 5231941 * 2 ^ 59
def prefixEnd_5231941 : Nat := 4983230072969 + 3 ^ 40 * 5231941 * 2
def baseEnd_5231941 : Nat := 2686500488965019740476247

theorem tailTrace_5231941 : CollatzResearch.WordTrace tailWord_5231941 prefixEnd_5231941 2686500488965019740476247 := by
  unfold tailWord_5231941
  simp only [CollatzResearch.WordTrace]
  refine ⟨190824565138578776229207677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127216376759052517486138451 190824565138578776229207677)
  ·
    refine ⟨71559211926967041085952879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190824565138578776229207677 71559211926967041085952879)
    ·
      refine ⟨107338817890450561628929319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71559211926967041085952879 107338817890450561628929319)
      ·
        refine ⟨161008226835675842443393979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107338817890450561628929319 161008226835675842443393979)
        ·
          refine ⟨241512340253513763665090969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161008226835675842443393979 241512340253513763665090969)
          ·
            refine ⟨181134255190135322748818227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241512340253513763665090969 181134255190135322748818227)
            ·
              refine ⟨271701382785202984123227341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181134255190135322748818227 271701382785202984123227341)
              ·
                refine ⟨101888018544451119046210253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271701382785202984123227341 101888018544451119046210253)
                ·
                  refine ⟨38208006954169169642328845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101888018544451119046210253 38208006954169169642328845)
                  ·
                    refine ⟨14328002607813438615873317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38208006954169169642328845 14328002607813438615873317)
                    ·
                      refine ⟨2686500488965019740476247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14328002607813438615873317 2686500488965019740476247)
                      ·
                        rfl

theorem cell23_5231941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_5231941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5231941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5231941 prefixEnd_5231941 := by exact prefixLift 5231941
  have htrace : WordTrace (prefixWord ++ tailWord_5231941) baseStart_5231941 baseEnd_5231941 := by
    simpa [prefixWord, tailWord_5231941, baseEnd_5231941] using wordTrace_append hprefix tailTrace_5231941
  have hstable : (prefixWord ++ tailWord_5231941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5231941).length < 2 ^ (prefixWord ++ tailWord_5231941).sum := by decide
  have hdescent : baseEnd_5231941 < baseStart_5231941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5231941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232002 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_5232002 : Nat := 118140960795 + 5232002 * 2 ^ 59
def prefixEnd_5232002 : Nat := 4983230072969 + 3 ^ 40 * 5232002 * 2
def baseEnd_5232002 : Nat := 895510603761648000604489

theorem tailTrace_5232002 : CollatzResearch.WordTrace tailWord_5232002 prefixEnd_5232002 895510603761648000604489 := by
  unfold tailWord_5232002
  simp only [CollatzResearch.WordTrace]
  refine ⟨47706697497839445911794565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127217859994238522431452173 47706697497839445911794565)
  ·
    refine ⟨8945005780844896108461481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47706697497839445911794565 8945005780844896108461481)
    ·
      refine ⟨6708754335633672081346111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8945005780844896108461481 6708754335633672081346111)
      ·
        refine ⟨10063131503450508122019167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6708754335633672081346111 10063131503450508122019167)
        ·
          refine ⟨15094697255175762183028751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10063131503450508122019167 15094697255175762183028751)
          ·
            refine ⟨22642045882763643274543127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15094697255175762183028751 22642045882763643274543127)
            ·
              refine ⟨33963068824145464911814691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22642045882763643274543127 33963068824145464911814691)
              ·
                refine ⟨50944603236218197367722037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33963068824145464911814691 50944603236218197367722037)
                ·
                  refine ⟨4776056553395456003223941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50944603236218197367722037 4776056553395456003223941)
                  ·
                    refine ⟨895510603761648000604489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4776056553395456003223941 895510603761648000604489)
                    ·
                      rfl

theorem cell23_5232002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_5232002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232002 prefixEnd_5232002 := by exact prefixLift 5232002
  have htrace : WordTrace (prefixWord ++ tailWord_5232002) baseStart_5232002 baseEnd_5232002 := by
    simpa [prefixWord, tailWord_5232002, baseEnd_5232002] using wordTrace_append hprefix tailTrace_5232002
  have hstable : (prefixWord ++ tailWord_5232002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232002).length < 2 ^ (prefixWord ++ tailWord_5232002).sum := by decide
  have hdescent : baseEnd_5232002 < baseStart_5232002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232035 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 4, 3, 2]
def baseStart_5232035 : Nat := 118140960795 + 5232035 * 2 ^ 59
def prefixEnd_5232035 : Nat := 4983230072969 + 3 ^ 40 * 5232035 * 2
def baseEnd_5232035 : Nat := 2686548756146542372700815

theorem tailTrace_5232035 : CollatzResearch.WordTrace tailWord_5232035 prefixEnd_5232035 2686548756146542372700815 := by
  unfold tailWord_5232035
  simp only [CollatzResearch.WordTrace]
  refine ⟨190827993600238230283129559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127218662400158820188753039 190827993600238230283129559)
  ·
    refine ⟨286241990400357345424694339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190827993600238230283129559 286241990400357345424694339)
    ·
      refine ⟨429362985600536018137041509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286241990400357345424694339 429362985600536018137041509)
      ·
        refine ⟨80505559800100503400695283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 429362985600536018137041509 80505559800100503400695283)
        ·
          refine ⟨120758339700150755101042925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80505559800100503400695283 120758339700150755101042925)
          ·
            refine ⟨45284377387556533162891097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120758339700150755101042925 45284377387556533162891097)
            ·
              refine ⟨33963283040667399872168323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45284377387556533162891097 33963283040667399872168323)
              ·
                refine ⟨50944924561001099808252485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33963283040667399872168323 50944924561001099808252485)
                ·
                  refine ⟨9552173355187706214047341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50944924561001099808252485 9552173355187706214047341)
                  ·
                    refine ⟨3582065008195389830267753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9552173355187706214047341 3582065008195389830267753)
                    ·
                      refine ⟨2686548756146542372700815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582065008195389830267753 2686548756146542372700815)
                      ·
                        rfl

theorem cell23_5232035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_5232035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232035 prefixEnd_5232035 := by exact prefixLift 5232035
  have htrace : WordTrace (prefixWord ++ tailWord_5232035) baseStart_5232035 baseEnd_5232035 := by
    simpa [prefixWord, tailWord_5232035, baseEnd_5232035] using wordTrace_append hprefix tailTrace_5232035
  have hstable : (prefixWord ++ tailWord_5232035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232035).length < 2 ^ (prefixWord ++ tailWord_5232035).sum := by decide
  have hdescent : baseEnd_5232035 < baseStart_5232035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232041 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 2, 10]
def baseStart_5232041 : Nat := 118140960795 + 5232041 * 2 ^ 59
def prefixEnd_5232041 : Nat := 4983230072969 + 3 ^ 40 * 5232041 * 2
def baseEnd_5232041 : Nat := 895517279010156449741929

theorem tailTrace_5232041 : CollatzResearch.WordTrace tailWord_5232041 prefixEnd_5232041 895517279010156449741929 := by
  unfold tailWord_5232041
  simp only [CollatzResearch.WordTrace]
  refine ⟨190828212438216493307847977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127218808292144328871898651 190828212438216493307847977)
  ·
    refine ⟨143121159328662369980885983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190828212438216493307847977 143121159328662369980885983)
    ·
      refine ⟨214681738992993554971328975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143121159328662369980885983 214681738992993554971328975)
      ·
        refine ⟨322022608489490332456993463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214681738992993554971328975 322022608489490332456993463)
        ·
          refine ⟨483033912734235498685490195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322022608489490332456993463 483033912734235498685490195)
          ·
            refine ⟨724550869101353248028235293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483033912734235498685490195 724550869101353248028235293)
            ·
              refine ⟨271706575913007468010588235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 724550869101353248028235293 271706575913007468010588235)
              ·
                refine ⟨407559863869511202015882353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271706575913007468010588235 407559863869511202015882353)
                ·
                  refine ⟨305669897902133401511911765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407559863869511202015882353 305669897902133401511911765)
                  ·
                    refine ⟨895517279010156449741929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 305669897902133401511911765 895517279010156449741929)
                    ·
                      rfl

theorem cell23_5232041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 10].length) (baseStart_5232041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232041 prefixEnd_5232041 := by exact prefixLift 5232041
  have htrace : WordTrace (prefixWord ++ tailWord_5232041) baseStart_5232041 baseEnd_5232041 := by
    simpa [prefixWord, tailWord_5232041, baseEnd_5232041] using wordTrace_append hprefix tailTrace_5232041
  have hstable : (prefixWord ++ tailWord_5232041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232041).length < 2 ^ (prefixWord ++ tailWord_5232041).sum := by decide
  have hdescent : baseEnd_5232041 < baseStart_5232041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232048 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_5232048 : Nat := 118140960795 + 5232048 * 2 ^ 59
def prefixEnd_5232048 : Nat := 4983230072969 + 3 ^ 40 * 5232048 * 2
def baseEnd_5232048 : Nat := 2686555431395050821838255

theorem tailTrace_5232048 : CollatzResearch.WordTrace tailWord_5232048 prefixEnd_5232048 2686555431395050821838255 := by
  unfold tailWord_5232048
  simp only [CollatzResearch.WordTrace]
  refine ⟨95414233874595566751676399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127218978499460755668901865 95414233874595566751676399)
  ·
    refine ⟨143121350811893350127514599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95414233874595566751676399 143121350811893350127514599)
    ·
      refine ⟨214682026217840025191271899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143121350811893350127514599 214682026217840025191271899)
      ·
        refine ⟨322023039326760037786907849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214682026217840025191271899 322023039326760037786907849)
        ·
          refine ⟨241517279495070028340180887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322023039326760037786907849 241517279495070028340180887)
          ·
            refine ⟨362275919242605042510271331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241517279495070028340180887 362275919242605042510271331)
            ·
              refine ⟨543413878863907563765406997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362275919242605042510271331 543413878863907563765406997)
              ·
                refine ⟨25472525571745667051503453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 543413878863907563765406997 25472525571745667051503453)
                ·
                  refine ⟨9552197089404625144313795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25472525571745667051503453 9552197089404625144313795)
                  ·
                    refine ⟨14328295634106937716470693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9552197089404625144313795 14328295634106937716470693)
                    ·
                      refine ⟨2686555431395050821838255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14328295634106937716470693 2686555431395050821838255)
                      ·
                        rfl

theorem cell23_5232048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_5232048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232048 prefixEnd_5232048 := by exact prefixLift 5232048
  have htrace : WordTrace (prefixWord ++ tailWord_5232048) baseStart_5232048 baseEnd_5232048 := by
    simpa [prefixWord, tailWord_5232048, baseEnd_5232048] using wordTrace_append hprefix tailTrace_5232048
  have hstable : (prefixWord ++ tailWord_5232048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232048).length < 2 ^ (prefixWord ++ tailWord_5232048).sum := by decide
  have hdescent : baseEnd_5232048 < baseStart_5232048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232076 : List Nat := [2, 2, 1, 4, 2, 3, 1, 3, 1, 1, 3]
def baseStart_5232076 : Nat := 118140960795 + 5232076 * 2 ^ 59
def prefixEnd_5232076 : Nat := 4983230072969 + 3 ^ 40 * 5232076 * 2
def baseEnd_5232076 : Nat := 2686569808853376712288127

theorem tailTrace_5232076 : CollatzResearch.WordTrace tailWord_5232076 prefixEnd_5232076 2686569808853376712288127 := by
  unfold tailWord_5232076
  simp only [CollatzResearch.WordTrace]
  refine ⟨95414744496544847142686041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127219659328726462856914721 95414744496544847142686041)
  ·
    refine ⟨71561058372408635357014531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95414744496544847142686041 71561058372408635357014531)
    ·
      refine ⟨107341587558612953035521797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71561058372408635357014531 107341587558612953035521797)
      ·
        refine ⟨20126547667239928694160337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107341587558612953035521797 20126547667239928694160337)
        ·
          refine ⟨15094910750429946520620253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20126547667239928694160337 15094910750429946520620253)
          ·
            refine ⟨5660591531411229945232595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15094910750429946520620253 5660591531411229945232595)
            ·
              refine ⟨8490887297116844917848893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5660591531411229945232595 8490887297116844917848893)
              ·
                refine ⟨3184082736418816844193335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8490887297116844917848893 3184082736418816844193335)
                ·
                  refine ⟨4776124104628225266290003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184082736418816844193335 4776124104628225266290003)
                  ·
                    refine ⟨7164186156942337899435005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4776124104628225266290003 7164186156942337899435005)
                    ·
                      refine ⟨2686569808853376712288127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7164186156942337899435005 2686569808853376712288127)
                      ·
                        rfl

theorem cell23_5232076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_5232076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232076 prefixEnd_5232076 := by exact prefixLift 5232076
  have htrace : WordTrace (prefixWord ++ tailWord_5232076) baseStart_5232076 baseEnd_5232076 := by
    simpa [prefixWord, tailWord_5232076, baseEnd_5232076] using wordTrace_append hprefix tailTrace_5232076
  have hstable : (prefixWord ++ tailWord_5232076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232076).length < 2 ^ (prefixWord ++ tailWord_5232076).sum := by decide
  have hdescent : baseEnd_5232076 < baseStart_5232076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232085 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_5232085 : Nat := 118140960795 + 5232085 * 2 ^ 59
def prefixEnd_5232085 : Nat := 4983230072969 + 3 ^ 40 * 5232085 * 2
def baseEnd_5232085 : Nat := 2686574430179267177075585

theorem tailTrace_5232085 : CollatzResearch.WordTrace tailWord_5232085 prefixEnd_5232085 2686574430179267177075585 := by
  unfold tailWord_5232085
  simp only [CollatzResearch.WordTrace]
  refine ⟨190829817250057088822449709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127219878166704725881633139 190829817250057088822449709)
  ·
    refine ⟨71561181468771408308418641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190829817250057088822449709 71561181468771408308418641)
    ·
      refine ⟨53670886101578556231313981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71561181468771408308418641 53670886101578556231313981)
      ·
        refine ⟨20126582288091958586742743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53670886101578556231313981 20126582288091958586742743)
        ·
          refine ⟨30189873432137937880114115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20126582288091958586742743 30189873432137937880114115)
          ·
            refine ⟨45284810148206906820171173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30189873432137937880114115 45284810148206906820171173)
            ·
              refine ⟨8490901902788795028782095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45284810148206906820171173 8490901902788795028782095)
              ·
                refine ⟨12736352854183192543173143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8490901902788795028782095 12736352854183192543173143)
                ·
                  refine ⟨19104529281274788814759715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12736352854183192543173143 19104529281274788814759715)
                  ·
                    refine ⟨28656793921912183222139573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19104529281274788814759715 28656793921912183222139573)
                    ·
                      refine ⟨2686574430179267177075585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28656793921912183222139573 2686574430179267177075585)
                      ·
                        rfl

theorem cell23_5232085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_5232085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232085 prefixEnd_5232085 := by exact prefixLift 5232085
  have htrace : WordTrace (prefixWord ++ tailWord_5232085) baseStart_5232085 baseEnd_5232085 := by
    simpa [prefixWord, tailWord_5232085, baseEnd_5232085] using wordTrace_append hprefix tailTrace_5232085
  have hstable : (prefixWord ++ tailWord_5232085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232085).length < 2 ^ (prefixWord ++ tailWord_5232085).sum := by decide
  have hdescent : baseEnd_5232085 < baseStart_5232085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232099 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 3, 2, 2]
def baseStart_5232099 : Nat := 118140960795 + 5232099 * 2 ^ 59
def prefixEnd_5232099 : Nat := 4983230072969 + 3 ^ 40 * 5232099 * 2
def baseEnd_5232099 : Nat := 2686581618908430122300521

theorem tailTrace_5232099 : CollatzResearch.WordTrace tailWord_5232099 prefixEnd_5232099 2686581618908430122300521 := by
  unfold tailWord_5232099
  simp only [CollatzResearch.WordTrace]
  refine ⟨190830327872006369213459351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127220218581337579475639567 190830327872006369213459351)
  ·
    refine ⟨286245491808009553820189027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190830327872006369213459351 286245491808009553820189027)
    ·
      refine ⟨429368237712014330730283541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286245491808009553820189027 429368237712014330730283541)
      ·
        refine ⟨20126636142750671752982041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 429368237712014330730283541 20126636142750671752982041)
        ·
          refine ⟨15094977107063003814736531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20126636142750671752982041 15094977107063003814736531)
          ·
            refine ⟨22642465660594505722104797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15094977107063003814736531 22642465660594505722104797)
            ·
              refine ⟨8490924622722939645789299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22642465660594505722104797 8490924622722939645789299)
              ·
                refine ⟨12736386934084409468683949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8490924622722939645789299 12736386934084409468683949)
                ·
                  refine ⟨4776145100281653550756481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12736386934084409468683949 4776145100281653550756481)
                  ·
                    refine ⟨3582108825211240163067361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4776145100281653550756481 3582108825211240163067361)
                    ·
                      refine ⟨2686581618908430122300521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582108825211240163067361 2686581618908430122300521)
                      ·
                        rfl

theorem cell23_5232099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_5232099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232099 prefixEnd_5232099 := by exact prefixLift 5232099
  have htrace : WordTrace (prefixWord ++ tailWord_5232099) baseStart_5232099 baseEnd_5232099 := by
    simpa [prefixWord, tailWord_5232099, baseEnd_5232099] using wordTrace_append hprefix tailTrace_5232099
  have hstable : (prefixWord ++ tailWord_5232099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232099).length < 2 ^ (prefixWord ++ tailWord_5232099).sum := by decide
  have hdescent : baseEnd_5232099 < baseStart_5232099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232109 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_5232109 : Nat := 118140960795 + 5232109 * 2 ^ 59
def prefixEnd_5232109 : Nat := 4983230072969 + 3 ^ 40 * 5232109 * 2
def baseEnd_5232109 : Nat := 895528917904991694391825

theorem tailTrace_5232109 : CollatzResearch.WordTrace tailWord_5232109 prefixEnd_5232109 895528917904991694391825 := by
  unfold tailWord_5232109
  simp only [CollatzResearch.WordTrace]
  refine ⟨190830692601970140921323381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127220461734646760614215587 190830692601970140921323381)
  ·
    refine ⟨17890377431434700711374067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190830692601970140921323381 17890377431434700711374067)
    ·
      refine ⟨26835566147152051067061101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17890377431434700711374067 26835566147152051067061101)
      ·
        refine ⟨10063337305182019150147913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26835566147152051067061101 10063337305182019150147913)
        ·
          refine ⟨7547502978886514362610935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10063337305182019150147913 7547502978886514362610935)
          ·
            refine ⟨11321254468329771543916403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7547502978886514362610935 11321254468329771543916403)
            ·
              refine ⟨16981881702494657315874605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11321254468329771543916403 16981881702494657315874605)
              ·
                refine ⟨6368205638435496493452977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16981881702494657315874605 6368205638435496493452977)
                ·
                  refine ⟨4776154228826622370089733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6368205638435496493452977 4776154228826622370089733)
                  ·
                    refine ⟨895528917904991694391825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4776154228826622370089733 895528917904991694391825)
                    ·
                      rfl

theorem cell23_5232109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_5232109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232109 prefixEnd_5232109 := by exact prefixLift 5232109
  have htrace : WordTrace (prefixWord ++ tailWord_5232109) baseStart_5232109 baseEnd_5232109 := by
    simpa [prefixWord, tailWord_5232109, baseEnd_5232109] using wordTrace_append hprefix tailTrace_5232109
  have hstable : (prefixWord ++ tailWord_5232109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232109).length < 2 ^ (prefixWord ++ tailWord_5232109).sum := by decide
  have hdescent : baseEnd_5232109 < baseStart_5232109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232115 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 3]
def baseStart_5232115 : Nat := 118140960795 + 5232115 * 2 ^ 59
def prefixEnd_5232115 : Nat := 4983230072969 + 3 ^ 40 * 5232115 * 2
def baseEnd_5232115 : Nat := 2686589834598902059700447

theorem tailTrace_5232115 : CollatzResearch.WordTrace tailWord_5232115 prefixEnd_5232115 2686589834598902059700447 := by
  unfold tailWord_5232115
  simp only [CollatzResearch.WordTrace]
  refine ⟨190830911439948403946041799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127220607626632269297361199 190830911439948403946041799)
  ·
    refine ⟨286246367159922605919062699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190830911439948403946041799 286246367159922605919062699)
    ·
      refine ⟨429369550739883908878594049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286246367159922605919062699 429369550739883908878594049)
      ·
        refine ⟨322027163054912931658945537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429369550739883908878594049 322027163054912931658945537)
        ·
          refine ⟨241520372291184698744209153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322027163054912931658945537 241520372291184698744209153)
          ·
            refine ⟨181140279218388524058156865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241520372291184698744209153 181140279218388524058156865)
            ·
              refine ⟨135855209413791393043617649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181140279218388524058156865 135855209413791393043617649)
              ·
                refine ⟨101891407060343544782713237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135855209413791393043617649 101891407060343544782713237)
                ·
                  refine ⟨4776159705953603661689683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101891407060343544782713237 4776159705953603661689683)
                  ·
                    refine ⟨7164239558930405492534525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4776159705953603661689683 7164239558930405492534525)
                    ·
                      refine ⟨2686589834598902059700447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7164239558930405492534525 2686589834598902059700447)
                      ·
                        rfl

theorem cell23_5232115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 3].length) (baseStart_5232115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232115 prefixEnd_5232115 := by exact prefixLift 5232115
  have htrace : WordTrace (prefixWord ++ tailWord_5232115) baseStart_5232115 baseEnd_5232115 := by
    simpa [prefixWord, tailWord_5232115, baseEnd_5232115] using wordTrace_append hprefix tailTrace_5232115
  have hstable : (prefixWord ++ tailWord_5232115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232115).length < 2 ^ (prefixWord ++ tailWord_5232115).sum := by decide
  have hdescent : baseEnd_5232115 < baseStart_5232115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232149 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_5232149 : Nat := 118140960795 + 5232149 * 2 ^ 59
def prefixEnd_5232149 : Nat := 4983230072969 + 3 ^ 40 * 5232149 * 2
def baseEnd_5232149 : Nat := 2686607292941154926675291

theorem tailTrace_5232149 : CollatzResearch.WordTrace tailWord_5232149 prefixEnd_5232149 2686607292941154926675291 := by
  unfold tailWord_5232149
  simp only [CollatzResearch.WordTrace]
  refine ⟨190832151521825227752779501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127221434347883485168519667 190832151521825227752779501)
  ·
    refine ⟨71562056820684460407292313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190832151521825227752779501 71562056820684460407292313)
    ·
      refine ⟨53671542615513345305469235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71562056820684460407292313 53671542615513345305469235)
      ·
        refine ⟨80507313923270017958203853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53671542615513345305469235 80507313923270017958203853)
        ·
          refine ⟨30190242721226256734326445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80507313923270017958203853 30190242721226256734326445)
          ·
            refine ⟨11321341020459846275372417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30190242721226256734326445 11321341020459846275372417)
            ·
              refine ⟨8491005765344884706529313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11321341020459846275372417 8491005765344884706529313)
              ·
                refine ⟨6368254324008663529896985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8491005765344884706529313 6368254324008663529896985)
                ·
                  refine ⟨4776190743006497647422739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6368254324008663529896985 4776190743006497647422739)
                  ·
                    refine ⟨7164286114509746471134109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4776190743006497647422739 7164286114509746471134109)
                    ·
                      refine ⟨2686607292941154926675291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7164286114509746471134109 2686607292941154926675291)
                      ·
                        rfl

theorem cell23_5232149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_5232149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232149 prefixEnd_5232149 := by exact prefixLift 5232149
  have htrace : WordTrace (prefixWord ++ tailWord_5232149) baseStart_5232149 baseEnd_5232149 := by
    simpa [prefixWord, tailWord_5232149, baseEnd_5232149] using wordTrace_append hprefix tailTrace_5232149
  have hstable : (prefixWord ++ tailWord_5232149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232149).length < 2 ^ (prefixWord ++ tailWord_5232149).sum := by decide
  have hdescent : baseEnd_5232149 < baseStart_5232149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232172 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 8, 2, 2]
def baseStart_5232172 : Nat := 118140960795 + 5232172 * 2 ^ 59
def prefixEnd_5232172 : Nat := 4983230072969 + 3 ^ 40 * 5232172 * 2
def baseEnd_5232172 : Nat := 2686619102996208336687685

theorem tailTrace_5232172 : CollatzResearch.WordTrace tailWord_5232172 prefixEnd_5232172 2686619102996208336687685 := by
  unfold tailWord_5232172
  simp only [CollatzResearch.WordTrace]
  refine ⟨95416495200370951340433385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127221993600494601787244513 95416495200370951340433385)
  ·
    refine ⟨71562371400278213505325039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95416495200370951340433385 71562371400278213505325039)
    ·
      refine ⟨107343557100417320257987559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71562371400278213505325039 107343557100417320257987559)
      ·
        refine ⟨161015335650625980386981339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107343557100417320257987559 161015335650625980386981339)
        ·
          refine ⟨241523003475938970580472009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161015335650625980386981339 241523003475938970580472009)
          ·
            refine ⟨181142252606954227935354007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241523003475938970580472009 181142252606954227935354007)
            ·
              refine ⟨271713378910431341903031011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181142252606954227935354007 271713378910431341903031011)
              ·
                refine ⟨407570068365647012854546517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271713378910431341903031011 407570068365647012854546517)
                ·
                  refine ⟨4776211738659925931889217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 407570068365647012854546517 4776211738659925931889217)
                  ·
                    refine ⟨3582158803994944448916913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4776211738659925931889217 3582158803994944448916913)
                    ·
                      refine ⟨2686619102996208336687685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582158803994944448916913 2686619102996208336687685)
                      ·
                        rfl

theorem cell23_5232172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_5232172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232172 prefixEnd_5232172 := by exact prefixLift 5232172
  have htrace : WordTrace (prefixWord ++ tailWord_5232172) baseStart_5232172 baseEnd_5232172 := by
    simpa [prefixWord, tailWord_5232172, baseEnd_5232172] using wordTrace_append hprefix tailTrace_5232172
  have hstable : (prefixWord ++ tailWord_5232172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232172).length < 2 ^ (prefixWord ++ tailWord_5232172).sum := by decide
  have hdescent : baseEnd_5232172 < baseStart_5232172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232212 : List Nat := [2, 4, 1, 1, 1, 2, 1, 6, 5]
def baseStart_5232212 : Nat := 118140960795 + 5232212 * 2 ^ 59
def prefixEnd_5232212 : Nat := 4983230072969 + 3 ^ 40 * 5232212 * 2
def baseEnd_5232212 : Nat := 298515515802487575576389

theorem tailTrace_5232212 : CollatzResearch.WordTrace tailWord_5232212 prefixEnd_5232212 298515515802487575576389 := by
  unfold tailWord_5232212
  simp only [CollatzResearch.WordTrace]
  refine ⟨95417224660298494756161445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127222966213731326341548593 95417224660298494756161445)
  ·
    refine ⟨17890729623805967766780271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95417224660298494756161445 17890729623805967766780271)
    ·
      refine ⟨26836094435708951650170407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17890729623805967766780271 26836094435708951650170407)
      ·
        refine ⟨40254141653563427475255611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26836094435708951650170407 40254141653563427475255611)
        ·
          refine ⟨60381212480345141212883417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40254141653563427475255611 60381212480345141212883417)
          ·
            refine ⟨45285909360258855909662563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60381212480345141212883417 45285909360258855909662563)
            ·
              refine ⟨67928864040388283864493845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45285909360258855909662563 67928864040388283864493845)
              ·
                refine ⟨3184165501893200806148149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67928864040388283864493845 3184165501893200806148149)
                ·
                  refine ⟨298515515802487575576389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3184165501893200806148149 298515515802487575576389)
                  ·
                    rfl

theorem cell23_5232212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_5232212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232212 prefixEnd_5232212 := by exact prefixLift 5232212
  have htrace : WordTrace (prefixWord ++ tailWord_5232212) baseStart_5232212 baseEnd_5232212 := by
    simpa [prefixWord, tailWord_5232212, baseEnd_5232212] using wordTrace_append hprefix tailTrace_5232212
  have hstable : (prefixWord ++ tailWord_5232212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232212).length < 2 ^ (prefixWord ++ tailWord_5232212).sum := by decide
  have hdescent : baseEnd_5232212 < baseStart_5232212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232246 : List Nat := [5, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_5232246 : Nat := 118140960795 + 5232246 * 2 ^ 59
def prefixEnd_5232246 : Nat := 4983230072969 + 3 ^ 40 * 5232246 * 2
def baseEnd_5232246 : Nat := 298517455618293449684705

theorem tailTrace_5232246 : CollatzResearch.WordTrace tailWord_5232246 prefixEnd_5232246 298517455618293449684705 := by
  unfold tailWord_5232246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11927230587654613332441287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127223792934982542212707061 11927230587654613332441287)
  ·
    refine ⟨17890845881481919998661931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11927230587654613332441287 17890845881481919998661931)
    ·
      refine ⟨26836268822222879997992897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17890845881481919998661931 26836268822222879997992897)
      ·
        refine ⟨20127201616667159998494673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26836268822222879997992897 20127201616667159998494673)
        ·
          refine ⟨15095401212500369998871005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20127201616667159998494673 15095401212500369998871005)
          ·
            refine ⟨5660775454687638749576627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15095401212500369998871005 5660775454687638749576627)
            ·
              refine ⟨8491163182031458124364941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5660775454687638749576627 8491163182031458124364941)
              ·
                refine ⟨3184186193261796796636853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8491163182031458124364941 3184186193261796796636853)
                ·
                  refine ⟨298517455618293449684705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3184186193261796796636853 298517455618293449684705)
                  ·
                    rfl

theorem cell23_5232246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_5232246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232246 prefixEnd_5232246 := by exact prefixLift 5232246
  have htrace : WordTrace (prefixWord ++ tailWord_5232246) baseStart_5232246 baseEnd_5232246 := by
    simpa [prefixWord, tailWord_5232246, baseEnd_5232246] using wordTrace_append hprefix tailTrace_5232246
  have hstable : (prefixWord ++ tailWord_5232246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232246).length < 2 ^ (prefixWord ++ tailWord_5232246).sum := by decide
  have hdescent : baseEnd_5232246 < baseStart_5232246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232352 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_5232352 : Nat := 118140960795 + 5232352 * 2 ^ 59
def prefixEnd_5232352 : Nat := 4983230072969 + 3 ^ 40 * 5232352 * 2
def baseEnd_5232352 : Nat := 2686711529514017632436857

theorem tailTrace_5232352 : CollatzResearch.WordTrace tailWord_5232352 prefixEnd_5232352 2686711529514017632436857 := by
  unfold tailWord_5232352
  simp only [CollatzResearch.WordTrace]
  refine ⟨95419777770044896711209655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127226370360059862281612873 95419777770044896711209655)
  ·
    refine ⟨143129666655067345066814483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95419777770044896711209655 143129666655067345066814483)
    ·
      refine ⟨214694499982601017600221725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143129666655067345066814483 214694499982601017600221725)
      ·
        refine ⟨80510437493475381600083147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214694499982601017600221725 80510437493475381600083147)
        ·
          refine ⟨120765656240213072400124721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80510437493475381600083147 120765656240213072400124721)
          ·
            refine ⟨90574242180159804300093541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120765656240213072400124721 90574242180159804300093541)
            ·
              refine ⟨16982670408779963306267539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90574242180159804300093541 16982670408779963306267539)
              ·
                refine ⟨25474005613169944959401309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16982670408779963306267539 25474005613169944959401309)
                ·
                  refine ⟨9552752104938729359775491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25474005613169944959401309 9552752104938729359775491)
                  ·
                    refine ⟨14329128157408094039663237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9552752104938729359775491 14329128157408094039663237)
                    ·
                      refine ⟨2686711529514017632436857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14329128157408094039663237 2686711529514017632436857)
                      ·
                        rfl

theorem cell23_5232352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_5232352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232352 prefixEnd_5232352 := by exact prefixLift 5232352
  have htrace : WordTrace (prefixWord ++ tailWord_5232352) baseStart_5232352 baseEnd_5232352 := by
    simpa [prefixWord, tailWord_5232352, baseEnd_5232352] using wordTrace_append hprefix tailTrace_5232352
  have hstable : (prefixWord ++ tailWord_5232352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232352).length < 2 ^ (prefixWord ++ tailWord_5232352).sum := by decide
  have hdescent : baseEnd_5232352 < baseStart_5232352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232362 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_5232362 : Nat := 118140960795 + 5232362 * 2 ^ 59
def prefixEnd_5232362 : Nat := 4983230072969 + 3 ^ 40 * 5232362 * 2
def baseEnd_5232362 : Nat := 895572221440187531103937

theorem tailTrace_5232362 : CollatzResearch.WordTrace tailWord_5232362 prefixEnd_5232362 895572221440187531103937 := by
  unfold tailWord_5232362
  simp only [CollatzResearch.WordTrace]
  refine ⟨47709980067513391282570835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127226613513369043420188893 47709980067513391282570835)
  ·
    refine ⟨71564970101270086923856253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47709980067513391282570835 71564970101270086923856253)
    ·
      refine ⟨26836863787976282596446095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71564970101270086923856253 26836863787976282596446095)
      ·
        refine ⟨40255295681964423894669143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26836863787976282596446095 40255295681964423894669143)
        ·
          refine ⟨60382943522946635842003715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40255295681964423894669143 60382943522946635842003715)
          ·
            refine ⟨90574415284419953763005573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60382943522946635842003715 90574415284419953763005573)
            ·
              refine ⟨16982702865828741330563545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90574415284419953763005573 16982702865828741330563545)
              ·
                refine ⟨12737027149371555997922659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16982702865828741330563545 12737027149371555997922659)
                ·
                  refine ⟨19105540724057333996883989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12737027149371555997922659 19105540724057333996883989)
                  ·
                    refine ⟨895572221440187531103937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19105540724057333996883989 895572221440187531103937)
                    ·
                      rfl

theorem cell23_5232362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_5232362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232362 prefixEnd_5232362 := by exact prefixLift 5232362
  have htrace : WordTrace (prefixWord ++ tailWord_5232362) baseStart_5232362 baseEnd_5232362 := by
    simpa [prefixWord, tailWord_5232362, baseEnd_5232362] using wordTrace_append hprefix tailTrace_5232362
  have hstable : (prefixWord ++ tailWord_5232362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232362).length < 2 ^ (prefixWord ++ tailWord_5232362).sum := by decide
  have hdescent : baseEnd_5232362 < baseStart_5232362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232369 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 4]
def baseStart_5232369 : Nat := 118140960795 + 5232369 * 2 ^ 59
def prefixEnd_5232369 : Nat := 4983230072969 + 3 ^ 40 * 5232369 * 2
def baseEnd_5232369 : Nat := 2686720258685144065924279

theorem tailTrace_5232369 : CollatzResearch.WordTrace tailWord_5232369 prefixEnd_5232369 2686720258685144065924279 := by
  unfold tailWord_5232369
  simp only [CollatzResearch.WordTrace]
  refine ⟨190840175581028205325788161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127226783720685470217192107 190840175581028205325788161)
  ·
    refine ⟨143130131685771153994341121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190840175581028205325788161 143130131685771153994341121)
    ·
      refine ⟨107347598764328365495755841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143130131685771153994341121 107347598764328365495755841)
      ·
        refine ⟨80510699073246274121816881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107347598764328365495755841 80510699073246274121816881)
        ·
          refine ⟨60383024304934705591362661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80510699073246274121816881 60383024304934705591362661)
          ·
            refine ⟨11321817057175257298380499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60383024304934705591362661 11321817057175257298380499)
            ·
              refine ⟨16982725585762885947570749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11321817057175257298380499 16982725585762885947570749)
              ·
                refine ⟨6368522094661082230339031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16982725585762885947570749 6368522094661082230339031)
                ·
                  refine ⟨9552783141991623345508547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6368522094661082230339031 9552783141991623345508547)
                  ·
                    refine ⟨14329174712987435018262821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9552783141991623345508547 14329174712987435018262821)
                    ·
                      refine ⟨2686720258685144065924279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14329174712987435018262821 2686720258685144065924279)
                      ·
                        rfl

theorem cell23_5232369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_5232369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232369 prefixEnd_5232369 := by exact prefixLift 5232369
  have htrace : WordTrace (prefixWord ++ tailWord_5232369) baseStart_5232369 baseEnd_5232369 := by
    simpa [prefixWord, tailWord_5232369, baseEnd_5232369] using wordTrace_append hprefix tailTrace_5232369
  have hstable : (prefixWord ++ tailWord_5232369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232369).length < 2 ^ (prefixWord ++ tailWord_5232369).sum := by decide
  have hdescent : baseEnd_5232369 < baseStart_5232369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232414 : List Nat := [4, 3, 2, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5232414 : Nat := 118140960795 + 5232414 * 2 ^ 59
def prefixEnd_5232414 : Nat := 4983230072969 + 3 ^ 40 * 5232414 * 2
def baseEnd_5232414 : Nat := 2686743365314596389861573

theorem tailTrace_5232414 : CollatzResearch.WordTrace tailWord_5232414 prefixEnd_5232414 2686743365314596389861573 := by
  unfold tailWord_5232414
  simp only [CollatzResearch.WordTrace]
  refine ⟨23855227108233147251397037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127227877910576785340784197 23855227108233147251397037)
  ·
    refine ⟨8945710165587430219273889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23855227108233147251397037 8945710165587430219273889)
    ·
      refine ⟨6709282624190572664455417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8945710165587430219273889 6709282624190572664455417)
      ·
        refine ⟨5031961968142929498341563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6709282624190572664455417 5031961968142929498341563)
        ·
          refine ⟨7547942952214394247512345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5031961968142929498341563 7547942952214394247512345)
          ·
            refine ⟨5660957214160795685634259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7547942952214394247512345 5660957214160795685634259)
            ·
              refine ⟨8491435821241193528451389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5660957214160795685634259 8491435821241193528451389)
              ·
                refine ⟨3184288432965447573169271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8491435821241193528451389 3184288432965447573169271)
                ·
                  refine ⟨4776432649448171359753907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184288432965447573169271 4776432649448171359753907)
                  ·
                    refine ⟨7164648974172257039630861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4776432649448171359753907 7164648974172257039630861)
                    ·
                      refine ⟨2686743365314596389861573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7164648974172257039630861 2686743365314596389861573)
                      ·
                        rfl

theorem cell23_5232414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5232414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232414 prefixEnd_5232414 := by exact prefixLift 5232414
  have htrace : WordTrace (prefixWord ++ tailWord_5232414) baseStart_5232414 baseEnd_5232414 := by
    simpa [prefixWord, tailWord_5232414, baseEnd_5232414] using wordTrace_append hprefix tailTrace_5232414
  have hstable : (prefixWord ++ tailWord_5232414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232414).length < 2 ^ (prefixWord ++ tailWord_5232414).sum := by decide
  have hdescent : baseEnd_5232414 < baseStart_5232414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232419 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 3]
def baseStart_5232419 : Nat := 118140960795 + 5232419 * 2 ^ 59
def prefixEnd_5232419 : Nat := 4983230072969 + 3 ^ 40 * 5232419 * 2
def baseEnd_5232419 : Nat := 2686745932717868870299049

theorem tailTrace_5232419 : CollatzResearch.WordTrace tailWord_5232419 prefixEnd_5232419 2686745932717868870299049 := by
  unfold tailWord_5232419
  simp only [CollatzResearch.WordTrace]
  refine ⟨190841999230847063865108311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127227999487231375910072207 190841999230847063865108311)
  ·
    refine ⟨286262998846270595797662467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190841999230847063865108311 286262998846270595797662467)
    ·
      refine ⟨429394498269405893696493701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286262998846270595797662467 429394498269405893696493701)
      ·
        refine ⟨80511468425513605068092569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 429394498269405893696493701 80511468425513605068092569)
        ·
          refine ⟨60383601319135203801069427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80511468425513605068092569 60383601319135203801069427)
          ·
            refine ⟨90575401978702805701604141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60383601319135203801069427 90575401978702805701604141)
            ·
              refine ⟨33965775742013552138101553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90575401978702805701604141 33965775742013552138101553)
              ·
                refine ⟨25474331806510164103576165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33965775742013552138101553 25474331806510164103576165)
                ·
                  refine ⟨4776437213720655769420531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25474331806510164103576165 4776437213720655769420531)
                  ·
                    refine ⟨7164655820580983654130797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4776437213720655769420531 7164655820580983654130797)
                    ·
                      refine ⟨2686745932717868870299049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7164655820580983654130797 2686745932717868870299049)
                      ·
                        rfl

theorem cell23_5232419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_5232419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232419 prefixEnd_5232419 := by exact prefixLift 5232419
  have htrace : WordTrace (prefixWord ++ tailWord_5232419) baseStart_5232419 baseEnd_5232419 := by
    simpa [prefixWord, tailWord_5232419, baseEnd_5232419] using wordTrace_append hprefix tailTrace_5232419
  have hstable : (prefixWord ++ tailWord_5232419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232419).length < 2 ^ (prefixWord ++ tailWord_5232419).sum := by decide
  have hdescent : baseEnd_5232419 < baseStart_5232419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232420 : List Nat := [2, 3, 1, 3, 2, 1, 3, 3, 1, 2, 2]
def baseStart_5232420 : Nat := 118140960795 + 5232420 * 2 ^ 59
def prefixEnd_5232420 : Nat := 4983230072969 + 3 ^ 40 * 5232420 * 2
def baseEnd_5232420 : Nat := 2686746446198523366386545

theorem tailTrace_5232420 : CollatzResearch.WordTrace tailWord_5232420 prefixEnd_5232420 2686746446198523366386545 := by
  unfold tailWord_5232420
  simp only [CollatzResearch.WordTrace]
  refine ⟨95421017851921720517947357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127228023802562294023929809 95421017851921720517947357)
  ·
    refine ⟨35782881694470645194230259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95421017851921720517947357 35782881694470645194230259)
    ·
      refine ⟨53674322541705967791345389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35782881694470645194230259 53674322541705967791345389)
      ·
        refine ⟨20127870953139737921754521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53674322541705967791345389 20127870953139737921754521)
        ·
          refine ⟨15095903214854803441315891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20127870953139737921754521 15095903214854803441315891)
          ·
            refine ⟨22643854822282205161973837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15095903214854803441315891 22643854822282205161973837)
            ·
              refine ⟨8491445558355826935740189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22643854822282205161973837 8491445558355826935740189)
              ·
                refine ⟨3184292084383435100902571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8491445558355826935740189 3184292084383435100902571)
                ·
                  refine ⟨4776438126575152651353857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184292084383435100902571 4776438126575152651353857)
                  ·
                    refine ⟨3582328594931364488515393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4776438126575152651353857 3582328594931364488515393)
                    ·
                      refine ⟨2686746446198523366386545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582328594931364488515393 2686746446198523366386545)
                      ·
                        rfl

theorem cell23_5232420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_5232420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232420 prefixEnd_5232420 := by exact prefixLift 5232420
  have htrace : WordTrace (prefixWord ++ tailWord_5232420) baseStart_5232420 baseEnd_5232420 := by
    simpa [prefixWord, tailWord_5232420, baseEnd_5232420] using wordTrace_append hprefix tailTrace_5232420
  have hstable : (prefixWord ++ tailWord_5232420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232420).length < 2 ^ (prefixWord ++ tailWord_5232420).sum := by decide
  have hdescent : baseEnd_5232420 < baseStart_5232420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232437 : List Nat := [1, 3, 3, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_5232437 : Nat := 118140960795 + 5232437 * 2 ^ 59
def prefixEnd_5232437 : Nat := 4983230072969 + 3 ^ 40 * 5232437 * 2
def baseEnd_5232437 : Nat := 2686755175369649799873967

theorem tailTrace_5232437 : CollatzResearch.WordTrace tailWord_5232437 prefixEnd_5232437 2686755175369649799873967 := by
  unfold tailWord_5232437
  simp only [CollatzResearch.WordTrace]
  refine ⟨190842655744781852939263565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127228437163187901959509043 190842655744781852939263565)
  ·
    refine ⟨71565995904293194852223837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190842655744781852939263565 71565995904293194852223837)
    ·
      refine ⟨26837248464109948069583939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71565995904293194852223837 26837248464109948069583939)
      ·
        refine ⟨40255872696164922104375909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26837248464109948069583939 40255872696164922104375909)
        ·
          refine ⟨7547976130530922894570483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40255872696164922104375909 7547976130530922894570483)
          ·
            refine ⟨11321964195796384341855725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7547976130530922894570483 11321964195796384341855725)
            ·
              refine ⟨4245736573423644128195897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11321964195796384341855725 4245736573423644128195897)
              ·
                refine ⟨3184302430067733096146923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4245736573423644128195897 3184302430067733096146923)
                ·
                  refine ⟨4776453645101599644220385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184302430067733096146923 4776453645101599644220385)
                  ·
                    refine ⟨3582340233826199733165289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4776453645101599644220385 3582340233826199733165289)
                    ·
                      refine ⟨2686755175369649799873967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582340233826199733165289 2686755175369649799873967)
                      ·
                        rfl

theorem cell23_5232437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_5232437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232437 prefixEnd_5232437 := by exact prefixLift 5232437
  have htrace : WordTrace (prefixWord ++ tailWord_5232437) baseStart_5232437 baseEnd_5232437 := by
    simpa [prefixWord, tailWord_5232437, baseEnd_5232437] using wordTrace_append hprefix tailTrace_5232437
  have hstable : (prefixWord ++ tailWord_5232437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232437).length < 2 ^ (prefixWord ++ tailWord_5232437).sum := by decide
  have hdescent : baseEnd_5232437 < baseStart_5232437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232472 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_5232472 : Nat := 118140960795 + 5232472 * 2 ^ 59
def prefixEnd_5232472 : Nat := 4983230072969 + 3 ^ 40 * 5232472 * 2
def baseEnd_5232472 : Nat := 2686773147192557162936305

theorem tailTrace_5232472 : CollatzResearch.WordTrace tailWord_5232472 prefixEnd_5232472 2686773147192557162936305 := by
  unfold tailWord_5232472
  simp only [CollatzResearch.WordTrace]
  refine ⟨95421966149827526958393835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127229288199770035944525113 95421966149827526958393835)
  ·
    refine ⟨143132949224741290437590753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95421966149827526958393835 143132949224741290437590753)
    ·
      refine ⟨107349711918555967828193065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143132949224741290437590753 107349711918555967828193065)
      ·
        refine ⟨80512283938916975871144799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107349711918555967828193065 80512283938916975871144799)
        ·
          refine ⟨120768425908375463806717199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80512283938916975871144799 120768425908375463806717199)
          ·
            refine ⟨181152638862563195710075799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120768425908375463806717199 181152638862563195710075799)
            ·
              refine ⟨271728958293844793565113699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181152638862563195710075799 271728958293844793565113699)
              ·
                refine ⟨407593437440767190347670549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271728958293844793565113699 407593437440767190347670549)
                ·
                  refine ⟨19105942380035962047547057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 407593437440767190347670549 19105942380035962047547057)
                  ·
                    refine ⟨14329456785026971535660293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19105942380035962047547057 14329456785026971535660293)
                    ·
                      refine ⟨2686773147192557162936305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14329456785026971535660293 2686773147192557162936305)
                      ·
                        rfl

theorem cell23_5232472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_5232472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232472 prefixEnd_5232472 := by exact prefixLift 5232472
  have htrace : WordTrace (prefixWord ++ tailWord_5232472) baseStart_5232472 baseEnd_5232472 := by
    simpa [prefixWord, tailWord_5232472, baseEnd_5232472] using wordTrace_append hprefix tailTrace_5232472
  have hstable : (prefixWord ++ tailWord_5232472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232472).length < 2 ^ (prefixWord ++ tailWord_5232472).sum := by decide
  have hdescent : baseEnd_5232472 < baseStart_5232472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232493 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_5232493 : Nat := 118140960795 + 5232493 * 2 ^ 59
def prefixEnd_5232493 : Nat := 4983230072969 + 3 ^ 40 * 5232493 * 2
def baseEnd_5232493 : Nat := 2686783930286301580773709

theorem tailTrace_5232493 : CollatzResearch.WordTrace tailWord_5232493 prefixEnd_5232493 2686783930286301580773709 := by
  unfold tailWord_5232493
  simp only [CollatzResearch.WordTrace]
  refine ⟨190844698232578974503302133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127229798821719316335534755 190844698232578974503302133)
  ·
    refine ⟨17891690459304278859684575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190844698232578974503302133 17891690459304278859684575)
    ·
      refine ⟨26837535688956418289526863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17891690459304278859684575 26837535688956418289526863)
      ·
        refine ⟨40256303533434627434290295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26837535688956418289526863 40256303533434627434290295)
        ·
          refine ⟨60384455300151941151435443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40256303533434627434290295 60384455300151941151435443)
          ·
            refine ⟨90576682950227911727153165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60384455300151941151435443 90576682950227911727153165)
            ·
              refine ⟨33966256106335466897682437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90576682950227911727153165 33966256106335466897682437)
              ·
                refine ⟨6368673019937900043315457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33966256106335466897682437 6368673019937900043315457)
                ·
                  refine ⟨4776504764953425032486593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6368673019937900043315457 4776504764953425032486593)
                  ·
                    refine ⟨3582378573715068774364945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4776504764953425032486593 3582378573715068774364945)
                    ·
                      refine ⟨2686783930286301580773709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582378573715068774364945 2686783930286301580773709)
                      ·
                        rfl

theorem cell23_5232493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_5232493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232493 prefixEnd_5232493 := by exact prefixLift 5232493
  have htrace : WordTrace (prefixWord ++ tailWord_5232493) baseStart_5232493 baseEnd_5232493 := by
    simpa [prefixWord, tailWord_5232493, baseEnd_5232493] using wordTrace_append hprefix tailTrace_5232493
  have hstable : (prefixWord ++ tailWord_5232493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232493).length < 2 ^ (prefixWord ++ tailWord_5232493).sum := by decide
  have hdescent : baseEnd_5232493 < baseStart_5232493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232510 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5232510 : Nat := 118140960795 + 5232510 * 2 ^ 59
def prefixEnd_5232510 : Nat := 4983230072969 + 3 ^ 40 * 5232510 * 2
def baseEnd_5232510 : Nat := 2686792659457428014261131

theorem tailTrace_5232510 : CollatzResearch.WordTrace tailWord_5232510 prefixEnd_5232510 2686792659457428014261131 := by
  unfold tailWord_5232510
  simp only [CollatzResearch.WordTrace]
  refine ⟨23855664784189673300833873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127230212182344924271113989 23855664784189673300833873)
  ·
    refine ⟨17891748588142254975625405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23855664784189673300833873 17891748588142254975625405)
    ·
      refine ⟨6709405720553345615859527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17891748588142254975625405 6709405720553345615859527)
      ·
        refine ⟨10064108580830018423789291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6709405720553345615859527 10064108580830018423789291)
        ·
          refine ⟨15096162871245027635683937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10064108580830018423789291 15096162871245027635683937)
          ·
            refine ⟨11322122153433770726762953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15096162871245027635683937 11322122153433770726762953)
            ·
              refine ⟨8491591615075328045072215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11322122153433770726762953 8491591615075328045072215)
              ·
                refine ⟨12737387422612992067608323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8491591615075328045072215 12737387422612992067608323)
                ·
                  refine ⟨19106081133919488101412485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12737387422612992067608323 19106081133919488101412485)
                  ·
                    refine ⟨3582390212609904019014841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19106081133919488101412485 3582390212609904019014841)
                    ·
                      refine ⟨2686792659457428014261131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582390212609904019014841 2686792659457428014261131)
                      ·
                        rfl

theorem cell23_5232510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5232510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232510 prefixEnd_5232510 := by exact prefixLift 5232510
  have htrace : WordTrace (prefixWord ++ tailWord_5232510) baseStart_5232510 baseEnd_5232510 := by
    simpa [prefixWord, tailWord_5232510, baseEnd_5232510] using wordTrace_append hprefix tailTrace_5232510
  have hstable : (prefixWord ++ tailWord_5232510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232510).length < 2 ^ (prefixWord ++ tailWord_5232510).sum := by decide
  have hdescent : baseEnd_5232510 < baseStart_5232510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232512 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 1, 7]
def baseStart_5232512 : Nat := 118140960795 + 5232512 * 2 ^ 59
def prefixEnd_5232512 : Nat := 4983230072969 + 3 ^ 40 * 5232512 * 2
def baseEnd_5232512 : Nat := 895597895472912335478707

theorem tailTrace_5232512 : CollatzResearch.WordTrace tailWord_5232512 prefixEnd_5232512 895597895472912335478707 := by
  unfold tailWord_5232512
  simp only [CollatzResearch.WordTrace]
  refine ⟨95422695609755070374121895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127230260813006760498829193 95422695609755070374121895)
  ·
    refine ⟨143134043414632605561182843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95422695609755070374121895 143134043414632605561182843)
    ·
      refine ⟨214701065121948908341774265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143134043414632605561182843 214701065121948908341774265)
      ·
        refine ⟨161025798841461681256330699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214701065121948908341774265 161025798841461681256330699)
        ·
          refine ⟨241538698262192521884496049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161025798841461681256330699 241538698262192521884496049)
          ·
            refine ⟨181154023696644391413372037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241538698262192521884496049 181154023696644391413372037)
            ·
              refine ⟨33966379443120823390007257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181154023696644391413372037 33966379443120823390007257)
              ·
                refine ⟨25474784582340617542505443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33966379443120823390007257 25474784582340617542505443)
                ·
                  refine ⟨38212176873510926313758165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25474784582340617542505443 38212176873510926313758165)
                  ·
                    refine ⟨895597895472912335478707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38212176873510926313758165 895597895472912335478707)
                    ·
                      rfl

theorem cell23_5232512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_5232512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232512 prefixEnd_5232512 := by exact prefixLift 5232512
  have htrace : WordTrace (prefixWord ++ tailWord_5232512) baseStart_5232512 baseEnd_5232512 := by
    simpa [prefixWord, tailWord_5232512, baseEnd_5232512] using wordTrace_append hprefix tailTrace_5232512
  have hstable : (prefixWord ++ tailWord_5232512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232512).length < 2 ^ (prefixWord ++ tailWord_5232512).sum := by decide
  have hdescent : baseEnd_5232512 < baseStart_5232512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232529 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 2, 5]
def baseStart_5232529 : Nat := 118140960795 + 5232529 * 2 ^ 59
def prefixEnd_5232529 : Nat := 4983230072969 + 3 ^ 40 * 5232529 * 2
def baseEnd_5232529 : Nat := 895600805196621146641181

theorem tailTrace_5232529 : CollatzResearch.WordTrace tailWord_5232529 prefixEnd_5232529 895600805196621146641181 := by
  unfold tailWord_5232529
  simp only [CollatzResearch.WordTrace]
  refine ⟨190846011260448552651612641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127230674173632368434408427 190846011260448552651612641)
  ·
    refine ⟨143134508445336414488709481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190846011260448552651612641 143134508445336414488709481)
    ·
      refine ⟨107350881334002310866532111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143134508445336414488709481 107350881334002310866532111)
      ·
        refine ⟨161026322001003466299798167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107350881334002310866532111 161026322001003466299798167)
        ·
          refine ⟨241539483001505199449697251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161026322001003466299798167 241539483001505199449697251)
          ·
            refine ⟨362309224502257799174545877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241539483001505199449697251 362309224502257799174545877)
            ·
              refine ⟨8491622449271667168153419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 362309224502257799174545877 8491622449271667168153419)
              ·
                refine ⟨12737433673907500752230129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8491622449271667168153419 12737433673907500752230129)
                ·
                  refine ⟨9553075255430625564172597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12737433673907500752230129 9553075255430625564172597)
                  ·
                    refine ⟨895600805196621146641181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9553075255430625564172597 895600805196621146641181)
                    ·
                      rfl

theorem cell23_5232529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_5232529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232529 prefixEnd_5232529 := by exact prefixLift 5232529
  have htrace : WordTrace (prefixWord ++ tailWord_5232529) baseStart_5232529 baseEnd_5232529 := by
    simpa [prefixWord, tailWord_5232529, baseEnd_5232529] using wordTrace_append hprefix tailTrace_5232529
  have hstable : (prefixWord ++ tailWord_5232529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232529).length < 2 ^ (prefixWord ++ tailWord_5232529).sum := by decide
  have hdescent : baseEnd_5232529 < baseStart_5232529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232549 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_5232549 : Nat := 118140960795 + 5232549 * 2 ^ 59
def prefixEnd_5232549 : Nat := 4983230072969 + 3 ^ 40 * 5232549 * 2
def baseEnd_5232549 : Nat := 2686812685202953361673451

theorem tailTrace_5232549 : CollatzResearch.WordTrace tailWord_5232549 prefixEnd_5232549 2686812685202953361673451 := by
  unfold tailWord_5232549
  simp only [CollatzResearch.WordTrace]
  refine ⟨190846740720376096067340701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127231160480250730711560467 190846740720376096067340701)
  ·
    refine ⟨71567527770141036025252763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190846740720376096067340701 71567527770141036025252763)
    ·
      refine ⟨107351291655211554037879145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71567527770141036025252763 107351291655211554037879145)
      ·
        refine ⟨80513468741408665528409359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107351291655211554037879145 80513468741408665528409359)
        ·
          refine ⟨120770203112112998292614039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80513468741408665528409359 120770203112112998292614039)
          ·
            refine ⟨181155304668169497438921059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120770203112112998292614039 181155304668169497438921059)
            ·
              refine ⟨271732957002254246158381589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181155304668169497438921059 271732957002254246158381589)
              ·
                refine ⟨12737482359480667788674137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 271732957002254246158381589 12737482359480667788674137)
                ·
                  refine ⟨9553111769610500841505603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12737482359480667788674137 9553111769610500841505603)
                  ·
                    refine ⟨14329667654415751262258405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9553111769610500841505603 14329667654415751262258405)
                    ·
                      refine ⟨2686812685202953361673451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14329667654415751262258405 2686812685202953361673451)
                      ·
                        rfl

theorem cell23_5232549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_5232549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232549 prefixEnd_5232549 := by exact prefixLift 5232549
  have htrace : WordTrace (prefixWord ++ tailWord_5232549) baseStart_5232549 baseEnd_5232549 := by
    simpa [prefixWord, tailWord_5232549, baseEnd_5232549] using wordTrace_append hprefix tailTrace_5232549
  have hstable : (prefixWord ++ tailWord_5232549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232549).length < 2 ^ (prefixWord ++ tailWord_5232549).sum := by decide
  have hdescent : baseEnd_5232549 < baseStart_5232549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232569 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 3]
def baseStart_5232569 : Nat := 118140960795 + 5232569 * 2 ^ 59
def prefixEnd_5232569 : Nat := 4983230072969 + 3 ^ 40 * 5232569 * 2
def baseEnd_5232569 : Nat := 2686822954816043283423359

theorem tailTrace_5232569 : CollatzResearch.WordTrace tailWord_5232569 prefixEnd_5232569 2686822954816043283423359 := by
  unfold tailWord_5232569
  simp only [CollatzResearch.WordTrace]
  refine ⟨190847470180303639483068761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127231646786869092988712507 190847470180303639483068761)
  ·
    refine ⟨143135602635227729612301571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190847470180303639483068761 143135602635227729612301571)
    ·
      refine ⟨214703403952841594418452357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143135602635227729612301571 214703403952841594418452357)
      ·
        refine ⟨40256888241157798953459817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214703403952841594418452357 40256888241157798953459817)
        ·
          refine ⟨30192666180868349215094863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40256888241157798953459817 30192666180868349215094863)
          ·
            refine ⟨45288999271302523822642295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30192666180868349215094863 45288999271302523822642295)
            ·
              refine ⟨67933498906953785733963443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45288999271302523822642295 67933498906953785733963443)
              ·
                refine ⟨101900248360430678600945165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67933498906953785733963443 101900248360430678600945165)
                ·
                  refine ⟨38212593135161504475354437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101900248360430678600945165 38212593135161504475354437)
                  ·
                    refine ⟨7164861212842782089128957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38212593135161504475354437 7164861212842782089128957)
                    ·
                      refine ⟨2686822954816043283423359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7164861212842782089128957 2686822954816043283423359)
                      ·
                        rfl

theorem cell23_5232569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_5232569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232569 prefixEnd_5232569 := by exact prefixLift 5232569
  have htrace : WordTrace (prefixWord ++ tailWord_5232569) baseStart_5232569 baseEnd_5232569 := by
    simpa [prefixWord, tailWord_5232569, baseEnd_5232569] using wordTrace_append hprefix tailTrace_5232569
  have hstable : (prefixWord ++ tailWord_5232569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232569).length < 2 ^ (prefixWord ++ tailWord_5232569).sum := by decide
  have hdescent : baseEnd_5232569 < baseStart_5232569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232690 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_5232690 : Nat := 118140960795 + 5232690 * 2 ^ 59
def prefixEnd_5232690 : Nat := 4983230072969 + 3 ^ 40 * 5232690 * 2
def baseEnd_5232690 : Nat := 2686885085975237310010303

theorem tailTrace_5232690 : CollatzResearch.WordTrace tailWord_5232690 prefixEnd_5232690 2686885085975237310010303 := by
  unfold tailWord_5232690
  simp only [CollatzResearch.WordTrace]
  refine ⟨47712970853216319287055881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127234588941910184765482349 47712970853216319287055881)
  ·
    refine ⟨35784728139912239465291911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47712970853216319287055881 35784728139912239465291911)
    ·
      refine ⟨53677092209868359197937867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35784728139912239465291911 53677092209868359197937867)
      ·
        refine ⟨80515638314802538796906801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53677092209868359197937867 80515638314802538796906801)
        ·
          refine ⟨60386728736101904097680101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80515638314802538796906801 60386728736101904097680101)
          ·
            refine ⟨11322511638019107018315019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60386728736101904097680101 11322511638019107018315019)
            ·
              refine ⟨16983767457028660527472529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11322511638019107018315019 16983767457028660527472529)
              ·
                refine ⟨12737825592771495395604397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16983767457028660527472529 12737825592771495395604397)
                ·
                  refine ⟨4776684597289310773351649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12737825592771495395604397 4776684597289310773351649)
                  ·
                    refine ⟨3582513447966983080013737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4776684597289310773351649 3582513447966983080013737)
                    ·
                      refine ⟨2686885085975237310010303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582513447966983080013737 2686885085975237310010303)
                      ·
                        rfl

theorem cell23_5232690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_5232690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232690 prefixEnd_5232690 := by exact prefixLift 5232690
  have htrace : WordTrace (prefixWord ++ tailWord_5232690) baseStart_5232690 baseEnd_5232690 := by
    simpa [prefixWord, tailWord_5232690, baseEnd_5232690] using wordTrace_append hprefix tailTrace_5232690
  have hstable : (prefixWord ++ tailWord_5232690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232690).length < 2 ^ (prefixWord ++ tailWord_5232690).sum := by decide
  have hdescent : baseEnd_5232690 < baseStart_5232690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232719 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_5232719 : Nat := 118140960795 + 5232719 * 2 ^ 59
def prefixEnd_5232719 : Nat := 4983230072969 + 3 ^ 40 * 5232719 * 2
def baseEnd_5232719 : Nat := 2686899976914217696547669

theorem tailTrace_5232719 : CollatzResearch.WordTrace tailWord_5232719 prefixEnd_5232719 2686899976914217696547669 := by
  unfold tailWord_5232719
  simp only [CollatzResearch.WordTrace]
  refine ⟨190852941129760215101029211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127235294086506810067352807 190852941129760215101029211)
  ·
    refine ⟨286279411694640322651543817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190852941129760215101029211 286279411694640322651543817)
    ·
      refine ⟨214709558770980241988657863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286279411694640322651543817 214709558770980241988657863)
      ·
        refine ⟨322064338156470362982986795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214709558770980241988657863 322064338156470362982986795)
        ·
          refine ⟨483096507234705544474480193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322064338156470362982986795 483096507234705544474480193)
          ·
            refine ⟨362322380426029158355860145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483096507234705544474480193 362322380426029158355860145)
            ·
              refine ⟨271741785319521868766895109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362322380426029158355860145 271741785319521868766895109)
              ·
                refine ⟨50951584747410350393792833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 271741785319521868766895109 50951584747410350393792833)
                ·
                  refine ⟨38213688560557762795344625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50951584747410350393792833 38213688560557762795344625)
                  ·
                    refine ⟨28660266420418322096508469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38213688560557762795344625 28660266420418322096508469)
                    ·
                      refine ⟨2686899976914217696547669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28660266420418322096508469 2686899976914217696547669)
                      ·
                        rfl

theorem cell23_5232719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_5232719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232719 prefixEnd_5232719 := by exact prefixLift 5232719
  have htrace : WordTrace (prefixWord ++ tailWord_5232719) baseStart_5232719 baseEnd_5232719 := by
    simpa [prefixWord, tailWord_5232719, baseEnd_5232719] using wordTrace_append hprefix tailTrace_5232719
  have hstable : (prefixWord ++ tailWord_5232719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232719).length < 2 ^ (prefixWord ++ tailWord_5232719).sum := by decide
  have hdescent : baseEnd_5232719 < baseStart_5232719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232734 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5232734 : Nat := 118140960795 + 5232734 * 2 ^ 59
def prefixEnd_5232734 : Nat := 4983230072969 + 3 ^ 40 * 5232734 * 2
def baseEnd_5232734 : Nat := 895635893041345045953367

theorem tailTrace_5232734 : CollatzResearch.WordTrace tailWord_5232734 prefixEnd_5232734 895635893041345045953367 := by
  unfold tailWord_5232734
  simp only [CollatzResearch.WordTrace]
  refine ⟨23856686028088234082853157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127235658816470581775216837 23856686028088234082853157)
  ·
    refine ⟨4473128630266543890534967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23856686028088234082853157 4473128630266543890534967)
    ·
      refine ⟨6709692945399815835802451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4473128630266543890534967 6709692945399815835802451)
      ·
        refine ⟨10064539418099723753703677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6709692945399815835802451 10064539418099723753703677)
        ·
          refine ⟨3774202281787396407638879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10064539418099723753703677 3774202281787396407638879)
          ·
            refine ⟨5661303422681094611458319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3774202281787396407638879 5661303422681094611458319)
            ·
              refine ⟨8491955134021641917187479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661303422681094611458319 8491955134021641917187479)
              ·
                refine ⟨12737932701032462875781219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8491955134021641917187479 12737932701032462875781219)
                ·
                  refine ⟨19106899051548694313671829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12737932701032462875781219 19106899051548694313671829)
                  ·
                    refine ⟨895635893041345045953367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19106899051548694313671829 895635893041345045953367)
                    ·
                      rfl

theorem cell23_5232734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5232734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232734 prefixEnd_5232734 := by exact prefixLift 5232734
  have htrace : WordTrace (prefixWord ++ tailWord_5232734) baseStart_5232734 baseEnd_5232734 := by
    simpa [prefixWord, tailWord_5232734, baseEnd_5232734] using wordTrace_append hprefix tailTrace_5232734
  have hstable : (prefixWord ++ tailWord_5232734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232734).length < 2 ^ (prefixWord ++ tailWord_5232734).sum := by decide
  have hdescent : baseEnd_5232734 < baseStart_5232734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232797 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_5232797 : Nat := 118140960795 + 5232797 * 2 ^ 59
def prefixEnd_5232797 : Nat := 4983230072969 + 3 ^ 40 * 5232797 * 2
def baseEnd_5232797 : Nat := 2686940028405268391372311

theorem tailTrace_5232797 : CollatzResearch.WordTrace tailWord_5232797 prefixEnd_5232797 2686940028405268391372311 := by
  unfold tailWord_5232797
  simp only [CollatzResearch.WordTrace]
  refine ⟨190855786023477634422368645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127237190682318422948245763 190855786023477634422368645)
  ·
    refine ⟨35785459879402056454194121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190855786023477634422368645 35785459879402056454194121)
    ·
      refine ⟨26839094909551542340645591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35785459879402056454194121 26839094909551542340645591)
      ·
        refine ⟨40258642364327313510968387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26839094909551542340645591 40258642364327313510968387)
        ·
          refine ⟨60387963546490970266452581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40258642364327313510968387 60387963546490970266452581)
          ·
            refine ⟨11322743164967056924959859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60387963546490970266452581 11322743164967056924959859)
            ·
              refine ⟨16984114747450585387439789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11322743164967056924959859 16984114747450585387439789)
              ·
                refine ⟨6369043030293969520289921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16984114747450585387439789 6369043030293969520289921)
                ·
                  refine ⟨4776782272720477140217441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6369043030293969520289921 4776782272720477140217441)
                  ·
                    refine ⟨3582586704540357855163081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4776782272720477140217441 3582586704540357855163081)
                    ·
                      refine ⟨2686940028405268391372311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582586704540357855163081 2686940028405268391372311)
                      ·
                        rfl

theorem cell23_5232797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_5232797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232797 prefixEnd_5232797 := by exact prefixLift 5232797
  have htrace : WordTrace (prefixWord ++ tailWord_5232797) baseStart_5232797 baseEnd_5232797 := by
    simpa [prefixWord, tailWord_5232797, baseEnd_5232797] using wordTrace_append hprefix tailTrace_5232797
  have hstable : (prefixWord ++ tailWord_5232797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232797).length < 2 ^ (prefixWord ++ tailWord_5232797).sum := by decide
  have hdescent : baseEnd_5232797 < baseStart_5232797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232814 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5232814 : Nat := 118140960795 + 5232814 * 2 ^ 59
def prefixEnd_5232814 : Nat := 4983230072969 + 3 ^ 40 * 5232814 * 2
def baseEnd_5232814 : Nat := 2686948757576394824859733

theorem tailTrace_5232814 : CollatzResearch.WordTrace tailWord_5232814 prefixEnd_5232814 2686948757576394824859733 := by
  unfold tailWord_5232814
  simp only [CollatzResearch.WordTrace]
  refine ⟨23857050758052005790717187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127237604042944030883824997 23857050758052005790717187)
  ·
    refine ⟨35785576137078008686075781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23857050758052005790717187 35785576137078008686075781)
    ·
      refine ⟨6709795525702126628639209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35785576137078008686075781 6709795525702126628639209)
      ·
        refine ⟨5032346644276594971479407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6709795525702126628639209 5032346644276594971479407)
        ·
          refine ⟨7548519966414892457219111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5032346644276594971479407 7548519966414892457219111)
          ·
            refine ⟨11322779949622338685828667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7548519966414892457219111 11322779949622338685828667)
            ·
              refine ⟨16984169924433508028743001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11322779949622338685828667 16984169924433508028743001)
              ·
                refine ⟨12738127443325131021557251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16984169924433508028743001 12738127443325131021557251)
                ·
                  refine ⟨19107191164987696532335877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12738127443325131021557251 19107191164987696532335877)
                  ·
                    refine ⟨3582598343435193099812977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19107191164987696532335877 3582598343435193099812977)
                    ·
                      refine ⟨2686948757576394824859733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582598343435193099812977 2686948757576394824859733)
                      ·
                        rfl

theorem cell23_5232814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5232814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232814 prefixEnd_5232814 := by exact prefixLift 5232814
  have htrace : WordTrace (prefixWord ++ tailWord_5232814) baseStart_5232814 baseEnd_5232814 := by
    simpa [prefixWord, tailWord_5232814, baseEnd_5232814] using wordTrace_append hprefix tailTrace_5232814
  have hstable : (prefixWord ++ tailWord_5232814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232814).length < 2 ^ (prefixWord ++ tailWord_5232814).sum := by decide
  have hdescent : baseEnd_5232814 < baseStart_5232814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232826 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_5232826 : Nat := 118140960795 + 5232826 * 2 ^ 59
def prefixEnd_5232826 : Nat := 4983230072969 + 3 ^ 40 * 5232826 * 2
def baseEnd_5232826 : Nat := 2686954919344248777909677

theorem tailTrace_5232826 : CollatzResearch.WordTrace tailWord_5232826 prefixEnd_5232826 2686954919344248777909677 := by
  unfold tailWord_5232826
  simp only [CollatzResearch.WordTrace]
  refine ⟨47714210935093143093793583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127237895826915048250116221 47714210935093143093793583)
  ·
    refine ⟨71571316402639714640690375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47714210935093143093793583 71571316402639714640690375)
    ·
      refine ⟨107356974603959571961035563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71571316402639714640690375 107356974603959571961035563)
      ·
        refine ⟨161035461905939357941553345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107356974603959571961035563 161035461905939357941553345)
        ·
          refine ⟨120776596429454518456165009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161035461905939357941553345 120776596429454518456165009)
          ·
            refine ⟨90582447322090888842123757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120776596429454518456165009 90582447322090888842123757)
            ·
              refine ⟨33968417745784083315796409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90582447322090888842123757 33968417745784083315796409)
              ·
                refine ⟨25476313309338062486847307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33968417745784083315796409 25476313309338062486847307)
                ·
                  refine ⟨38214469964007093730270961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25476313309338062486847307 38214469964007093730270961)
                  ·
                    refine ⟨28660852473005320297703221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38214469964007093730270961 28660852473005320297703221)
                    ·
                      refine ⟨2686954919344248777909677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28660852473005320297703221 2686954919344248777909677)
                      ·
                        rfl

theorem cell23_5232826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_5232826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232826 prefixEnd_5232826 := by exact prefixLift 5232826
  have htrace : WordTrace (prefixWord ++ tailWord_5232826) baseStart_5232826 baseEnd_5232826 := by
    simpa [prefixWord, tailWord_5232826, baseEnd_5232826] using wordTrace_append hprefix tailTrace_5232826
  have hstable : (prefixWord ++ tailWord_5232826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232826).length < 2 ^ (prefixWord ++ tailWord_5232826).sum := by decide
  have hdescent : baseEnd_5232826 < baseStart_5232826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232867 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 2, 5]
def baseStart_5232867 : Nat := 118140960795 + 5232867 * 2 ^ 59
def prefixEnd_5232867 : Nat := 4983230072969 + 3 ^ 40 * 5232867 * 2
def baseEnd_5232867 : Nat := 895658657350361039165663

theorem tailTrace_5232867 : CollatzResearch.WordTrace tailWord_5232867 prefixEnd_5232867 895658657350361039165663 := by
  unfold tailWord_5232867
  simp only [CollatzResearch.WordTrace]
  refine ⟨190858339133224036377416855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127238892755482690918277903 190858339133224036377416855)
  ·
    refine ⟨286287508699836054566125283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190858339133224036377416855 286287508699836054566125283)
    ·
      refine ⟨429431263049754081849187925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286287508699836054566125283 429431263049754081849187925)
      ·
        refine ⟨5032397613864305646670171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 429431263049754081849187925 5032397613864305646670171)
        ·
          refine ⟨7548596420796458470005257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5032397613864305646670171 7548596420796458470005257)
          ·
            refine ⟨5661447315597343852503943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7548596420796458470005257 5661447315597343852503943)
            ·
              refine ⟨8492170973396015778755915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661447315597343852503943 8492170973396015778755915)
              ·
                refine ⟨12738256460094023668133873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8492170973396015778755915 12738256460094023668133873)
                ·
                  refine ⟨9553692345070517751100405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12738256460094023668133873 9553692345070517751100405)
                  ·
                    refine ⟨895658657350361039165663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9553692345070517751100405 895658657350361039165663)
                    ·
                      rfl

theorem cell23_5232867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 5].length) (baseStart_5232867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232867 prefixEnd_5232867 := by exact prefixLift 5232867
  have htrace : WordTrace (prefixWord ++ tailWord_5232867) baseStart_5232867 baseEnd_5232867 := by
    simpa [prefixWord, tailWord_5232867, baseEnd_5232867] using wordTrace_append hprefix tailTrace_5232867
  have hstable : (prefixWord ++ tailWord_5232867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232867).length < 2 ^ (prefixWord ++ tailWord_5232867).sum := by decide
  have hdescent : baseEnd_5232867 < baseStart_5232867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232876 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 8]
def baseStart_5232876 : Nat := 118140960795 + 5232876 * 2 ^ 59
def prefixEnd_5232876 : Nat := 4983230072969 + 3 ^ 40 * 5232876 * 2
def baseEnd_5232876 : Nat := 298553399264108175809383

theorem tailTrace_5232876 : CollatzResearch.WordTrace tailWord_5232876 prefixEnd_5232876 298553399264108175809383 := by
  unfold tailWord_5232876
  simp only [CollatzResearch.WordTrace]
  refine ⟨95429333695095715457247241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127239111593460953942996321 95429333695095715457247241)
  ·
    refine ⟨71572000271321786592935431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95429333695095715457247241 71572000271321786592935431)
    ·
      refine ⟨107358000406982679889403147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71572000271321786592935431 107358000406982679889403147)
      ·
        refine ⟨161037000610474019834104721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107358000406982679889403147 161037000610474019834104721)
        ·
          refine ⟨120777750457855514875578541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161037000610474019834104721 120777750457855514875578541)
          ·
            refine ⟨45291656421695818078341953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120777750457855514875578541 45291656421695818078341953)
            ·
              refine ⟨33968742316271863558756465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45291656421695818078341953 33968742316271863558756465)
              ·
                refine ⟨25476556737203897669067349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33968742316271863558756465 25476556737203897669067349)
                ·
                  refine ⟨298553399264108175809383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25476556737203897669067349 298553399264108175809383)
                  ·
                    rfl

theorem cell23_5232876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_5232876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232876 prefixEnd_5232876 := by exact prefixLift 5232876
  have htrace : WordTrace (prefixWord ++ tailWord_5232876) baseStart_5232876 baseEnd_5232876 := by
    simpa [prefixWord, tailWord_5232876, baseEnd_5232876] using wordTrace_append hprefix tailTrace_5232876
  have hstable : (prefixWord ++ tailWord_5232876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232876).length < 2 ^ (prefixWord ++ tailWord_5232876).sum := by decide
  have hdescent : baseEnd_5232876 < baseStart_5232876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232896 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_5232896 : Nat := 118140960795 + 5232896 * 2 ^ 59
def prefixEnd_5232896 : Nat := 4983230072969 + 3 ^ 40 * 5232896 * 2
def baseEnd_5232896 : Nat := 2686990862990063504034355

theorem tailTrace_5232896 : CollatzResearch.WordTrace tailWord_5232896 prefixEnd_5232896 2686990862990063504034355 := by
  unfold tailWord_5232896
  simp only [CollatzResearch.WordTrace]
  refine ⟨95429698425059487165111271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127239597900079316220148361 95429698425059487165111271)
  ·
    refine ⟨143144547637589230747666907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95429698425059487165111271 143144547637589230747666907)
    ·
      refine ⟨214716821456383846121500361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143144547637589230747666907 214716821456383846121500361)
      ·
        refine ⟨161037616092287884591125271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214716821456383846121500361 161037616092287884591125271)
        ·
          refine ⟨241556424138431826886687907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161037616092287884591125271 241556424138431826886687907)
          ·
            refine ⟨362334636207647740330031861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241556424138431826886687907 362334636207647740330031861)
            ·
              refine ⟨33968872144466975655940487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 362334636207647740330031861 33968872144466975655940487)
              ·
                refine ⟨50953308216700463483910731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33968872144466975655940487 50953308216700463483910731)
                ·
                  refine ⟨76429962325050695225866097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50953308216700463483910731 76429962325050695225866097)
                  ·
                    refine ⟨57322471743788021419399573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76429962325050695225866097 57322471743788021419399573)
                    ·
                      refine ⟨2686990862990063504034355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57322471743788021419399573 2686990862990063504034355)
                      ·
                        rfl

theorem cell23_5232896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_5232896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232896 prefixEnd_5232896 := by exact prefixLift 5232896
  have htrace : WordTrace (prefixWord ++ tailWord_5232896) baseStart_5232896 baseEnd_5232896 := by
    simpa [prefixWord, tailWord_5232896, baseEnd_5232896] using wordTrace_append hprefix tailTrace_5232896
  have hstable : (prefixWord ++ tailWord_5232896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232896).length < 2 ^ (prefixWord ++ tailWord_5232896).sum := by decide
  have hdescent : baseEnd_5232896 < baseStart_5232896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232910 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_5232910 : Nat := 118140960795 + 5232910 * 2 ^ 59
def prefixEnd_5232910 : Nat := 4983230072969 + 3 ^ 40 * 5232910 * 2
def baseEnd_5232910 : Nat := 298555339079914049917699

theorem tailTrace_5232910 : CollatzResearch.WordTrace tailWord_5232910 prefixEnd_5232910 298555339079914049917699 := by
  unfold tailWord_5232910
  simp only [CollatzResearch.WordTrace]
  refine ⟨23857488434008531840154023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127239938314712169814154789 23857488434008531840154023)
  ·
    refine ⟨35786232651012797760231035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23857488434008531840154023 35786232651012797760231035)
    ·
      refine ⟨53679348976519196640346553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35786232651012797760231035 53679348976519196640346553)
      ·
        refine ⟨40259511732389397480259915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53679348976519196640346553 40259511732389397480259915)
        ·
          refine ⟨60389267598584096220389873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40259511732389397480259915 60389267598584096220389873)
          ·
            refine ⟨45291950698938072165292405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60389267598584096220389873 45291950698938072165292405)
            ·
              refine ⟨4246120378025444265496163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45291950698938072165292405 4246120378025444265496163)
              ·
                refine ⟨6369180567038166398244245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4246120378025444265496163 6369180567038166398244245)
                ·
                  refine ⟨298555339079914049917699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6369180567038166398244245 298555339079914049917699)
                  ·
                    rfl

theorem cell23_5232910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_5232910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232910 prefixEnd_5232910 := by exact prefixLift 5232910
  have htrace : WordTrace (prefixWord ++ tailWord_5232910) baseStart_5232910 baseEnd_5232910 := by
    simpa [prefixWord, tailWord_5232910, baseEnd_5232910] using wordTrace_append hprefix tailTrace_5232910
  have hstable : (prefixWord ++ tailWord_5232910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232910).length < 2 ^ (prefixWord ++ tailWord_5232910).sum := by decide
  have hdescent : baseEnd_5232910 < baseStart_5232910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232920 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 3, 1, 3]
def baseStart_5232920 : Nat := 118140960795 + 5232920 * 2 ^ 59
def prefixEnd_5232920 : Nat := 4983230072969 + 3 ^ 40 * 5232920 * 2
def baseEnd_5232920 : Nat := 2687003186525771410134245

theorem tailTrace_5232920 : CollatzResearch.WordTrace tailWord_5232920 prefixEnd_5232920 2687003186525771410134245 := by
  unfold tailWord_5232920
  simp only [CollatzResearch.WordTrace]
  refine ⟨95430136101016013214548107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127240181468021350952730809 95430136101016013214548107)
  ·
    refine ⟨143145204151524019821822161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95430136101016013214548107 143145204151524019821822161)
    ·
      refine ⟨107358903113643014866366621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143145204151524019821822161 107358903113643014866366621)
      ·
        refine ⟨40259588667616130574887483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107358903113643014866366621 40259588667616130574887483)
        ·
          refine ⟨60389383001424195862331225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40259588667616130574887483 60389383001424195862331225)
          ·
            refine ⟨45292037251068146896748419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60389383001424195862331225 45292037251068146896748419)
            ·
              refine ⟨67938055876602220345122629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45292037251068146896748419 67938055876602220345122629)
              ·
                refine ⟨12738385476862916314710493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67938055876602220345122629 12738385476862916314710493)
                ·
                  refine ⟨4776894553823593618016435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12738385476862916314710493 4776894553823593618016435)
                  ·
                    refine ⟨7165341830735390427024653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4776894553823593618016435 7165341830735390427024653)
                    ·
                      refine ⟨2687003186525771410134245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7165341830735390427024653 2687003186525771410134245)
                      ·
                        rfl

theorem cell23_5232920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_5232920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232920 prefixEnd_5232920 := by exact prefixLift 5232920
  have htrace : WordTrace (prefixWord ++ tailWord_5232920) baseStart_5232920 baseEnd_5232920 := by
    simpa [prefixWord, tailWord_5232920, baseEnd_5232920] using wordTrace_append hprefix tailTrace_5232920
  have hstable : (prefixWord ++ tailWord_5232920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232920).length < 2 ^ (prefixWord ++ tailWord_5232920).sum := by decide
  have hdescent : baseEnd_5232920 < baseStart_5232920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232923 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 1, 5]
def baseStart_5232923 : Nat := 118140960795 + 5232923 * 2 ^ 59
def prefixEnd_5232923 : Nat := 4983230072969 + 3 ^ 40 * 5232923 * 2
def baseEnd_5232923 : Nat := 895668242322578299465577

theorem tailTrace_5232923 : CollatzResearch.WordTrace tailWord_5232923 prefixEnd_5232923 895668242322578299465577 := by
  unfold tailWord_5232923
  simp only [CollatzResearch.WordTrace]
  refine ⟨190860381621021157941455423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127240254414014105294303615 190860381621021157941455423)
  ·
    refine ⟨286290572431531736912183135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190860381621021157941455423 286290572431531736912183135)
    ·
      refine ⟨429435858647297605368274703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286290572431531736912183135 429435858647297605368274703)
      ·
        refine ⟨644153787970946408052412055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429435858647297605368274703 644153787970946408052412055)
        ·
          refine ⟨966230681956419612078618083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644153787970946408052412055 966230681956419612078618083)
          ·
            refine ⟨1449346022934629418117927125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966230681956419612078618083 1449346022934629418117927125)
            ·
              refine ⟨33969047412530376987138917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1449346022934629418117927125 33969047412530376987138917)
              ·
                refine ⟨6369196389849445685088547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33969047412530376987138917 6369196389849445685088547)
                ·
                  refine ⟨9553794584774168527632821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6369196389849445685088547 9553794584774168527632821)
                  ·
                    refine ⟨895668242322578299465577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9553794584774168527632821 895668242322578299465577)
                    ·
                      rfl

theorem cell23_5232923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 5].length) (baseStart_5232923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232923 prefixEnd_5232923 := by exact prefixLift 5232923
  have htrace : WordTrace (prefixWord ++ tailWord_5232923) baseStart_5232923 baseEnd_5232923 := by
    simpa [prefixWord, tailWord_5232923, baseEnd_5232923] using wordTrace_append hprefix tailTrace_5232923
  have hstable : (prefixWord ++ tailWord_5232923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232923).length < 2 ^ (prefixWord ++ tailWord_5232923).sum := by decide
  have hdescent : baseEnd_5232923 < baseStart_5232923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232963 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 5]
def baseStart_5232963 : Nat := 118140960795 + 5232963 * 2 ^ 59
def prefixEnd_5232963 : Nat := 4983230072969 + 3 ^ 40 * 5232963 * 2
def baseEnd_5232963 : Nat := 2687025266193914741896547

theorem tailTrace_5232963 : CollatzResearch.WordTrace tailWord_5232963 prefixEnd_5232963 2687025266193914741896547 := by
  unfold tailWord_5232963
  simp only [CollatzResearch.WordTrace]
  refine ⟨190861840540876244772911543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127241227027250829848607695 190861840540876244772911543)
  ·
    refine ⟨286292760811314367159367315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190861840540876244772911543 286292760811314367159367315)
    ·
      refine ⟨429439141216971550739050973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286292760811314367159367315 429439141216971550739050973)
      ·
        refine ⟨161039677956364331527144115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 429439141216971550739050973 161039677956364331527144115)
        ·
          refine ⟨241559516934546497290716173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161039677956364331527144115 241559516934546497290716173)
          ·
            refine ⟨90584818850454936484018565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241559516934546497290716173 90584818850454936484018565)
            ·
              refine ⟨16984653534460300590753481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90584818850454936484018565 16984653534460300590753481)
              ·
                refine ⟨12738490150845225443065111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16984653534460300590753481 12738490150845225443065111)
                ·
                  refine ⟨19107735226267838164597667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12738490150845225443065111 19107735226267838164597667)
                  ·
                    refine ⟨28661602839401757246896501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19107735226267838164597667 28661602839401757246896501)
                    ·
                      refine ⟨2687025266193914741896547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28661602839401757246896501 2687025266193914741896547)
                      ·
                        rfl

theorem cell23_5232963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_5232963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232963 prefixEnd_5232963 := by exact prefixLift 5232963
  have htrace : WordTrace (prefixWord ++ tailWord_5232963) baseStart_5232963 baseEnd_5232963 := by
    simpa [prefixWord, tailWord_5232963, baseEnd_5232963] using wordTrace_append hprefix tailTrace_5232963
  have hstable : (prefixWord ++ tailWord_5232963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232963).length < 2 ^ (prefixWord ++ tailWord_5232963).sum := by decide
  have hdescent : baseEnd_5232963 < baseStart_5232963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232977 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 4]
def baseStart_5232977 : Nat := 118140960795 + 5232977 * 2 ^ 59
def prefixEnd_5232977 : Nat := 4983230072969 + 3 ^ 40 * 5232977 * 2
def baseEnd_5232977 : Nat := 2687032454923077687121483

theorem tailTrace_5232977 : CollatzResearch.WordTrace tailWord_5232977 prefixEnd_5232977 2687032454923077687121483 := by
  unfold tailWord_5232977
  simp only [CollatzResearch.WordTrace]
  refine ⟨190862351162825525163921185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127241567441883683442614123 190862351162825525163921185)
  ·
    refine ⟨143146763372119143872940889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190862351162825525163921185 143146763372119143872940889)
    ·
      refine ⟨107360072529089357904705667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143146763372119143872940889 107360072529089357904705667)
      ·
        refine ⟨161040108793634036857058501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107360072529089357904705667 161040108793634036857058501)
        ·
          refine ⟨30195020398806381910698469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161040108793634036857058501 30195020398806381910698469)
          ·
            refine ⟨5661566324776196608255963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30195020398806381910698469 5661566324776196608255963)
            ·
              refine ⟨8492349487164294912383945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5661566324776196608255963 8492349487164294912383945)
              ·
                refine ⟨6369262115373221184287959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8492349487164294912383945 6369262115373221184287959)
                ·
                  refine ⟨9553893173059831776431939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6369262115373221184287959 9553893173059831776431939)
                  ·
                    refine ⟨14330839759589747664647909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9553893173059831776431939 14330839759589747664647909)
                    ·
                      refine ⟨2687032454923077687121483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14330839759589747664647909 2687032454923077687121483)
                      ·
                        rfl

theorem cell23_5232977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_5232977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232977 prefixEnd_5232977 := by exact prefixLift 5232977
  have htrace : WordTrace (prefixWord ++ tailWord_5232977) baseStart_5232977 baseEnd_5232977 := by
    simpa [prefixWord, tailWord_5232977, baseEnd_5232977] using wordTrace_append hprefix tailTrace_5232977
  have hstable : (prefixWord ++ tailWord_5232977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232977).length < 2 ^ (prefixWord ++ tailWord_5232977).sum := by decide
  have hdescent : baseEnd_5232977 < baseStart_5232977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5232994 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_5232994 : Nat := 118140960795 + 5232994 * 2 ^ 59
def prefixEnd_5232994 : Nat := 4983230072969 + 3 ^ 40 * 5232994 * 2
def baseEnd_5232994 : Nat := 2687041184094204120608905

theorem tailTrace_5232994 : CollatzResearch.WordTrace tailWord_5232994 prefixEnd_5232994 2687041184094204120608905 := by
  unfold tailWord_5232994
  simp only [CollatzResearch.WordTrace]
  refine ⟨47715742800940984266822509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127241980802509291378193357 47715742800940984266822509)
  ·
    refine ⟨17893403550352869100058441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47715742800940984266822509 17893403550352869100058441)
    ·
      refine ⟨13420052662764651825043831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17893403550352869100058441 13420052662764651825043831)
      ·
        refine ⟨20130078994146977737565747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13420052662764651825043831 20130078994146977737565747)
        ·
          refine ⟨30195118491220466606348621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20130078994146977737565747 30195118491220466606348621)
          ·
            refine ⟨11323169434207674977380733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30195118491220466606348621 11323169434207674977380733)
            ·
              refine ⟨4246188537827878116517775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11323169434207674977380733 4246188537827878116517775)
              ·
                refine ⟨6369282806741817174776663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4246188537827878116517775 6369282806741817174776663)
                ·
                  refine ⟨9553924210112725762164995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6369282806741817174776663 9553924210112725762164995)
                  ·
                    refine ⟨14330886315169088643247493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9553924210112725762164995 14330886315169088643247493)
                    ·
                      refine ⟨2687041184094204120608905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14330886315169088643247493 2687041184094204120608905)
                      ·
                        rfl

theorem cell23_5232994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_5232994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5232994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5232994 prefixEnd_5232994 := by exact prefixLift 5232994
  have htrace : WordTrace (prefixWord ++ tailWord_5232994) baseStart_5232994 baseEnd_5232994 := by
    simpa [prefixWord, tailWord_5232994, baseEnd_5232994] using wordTrace_append hprefix tailTrace_5232994
  have hstable : (prefixWord ++ tailWord_5232994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5232994).length < 2 ^ (prefixWord ++ tailWord_5232994).sum := by decide
  have hdescent : baseEnd_5232994 < baseStart_5232994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5232994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233027 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 3]
def baseStart_5233027 : Nat := 118140960795 + 5233027 * 2 ^ 59
def prefixEnd_5233027 : Nat := 4983230072969 + 3 ^ 40 * 5233027 * 2
def baseEnd_5233027 : Nat := 2687058128955802491496253

theorem tailTrace_5233027 : CollatzResearch.WordTrace tailWord_5233027 prefixEnd_5233027 2687058128955802491496253 := by
  unfold tailWord_5233027
  simp only [CollatzResearch.WordTrace]
  refine ⟨190864174812644383703241335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127242783208429589135494223 190864174812644383703241335)
  ·
    refine ⟨286296262218966575554862003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190864174812644383703241335 286296262218966575554862003)
    ·
      refine ⟨429444393328449863332293005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286296262218966575554862003 429444393328449863332293005)
      ·
        refine ⟨161041647498168698749609877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 429444393328449863332293005 161041647498168698749609877)
        ·
          refine ⟨7548827226476657753887963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 161041647498168698749609877 7548827226476657753887963)
          ·
            refine ⟨11323240839714986630831945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7548827226476657753887963 11323240839714986630831945)
            ·
              refine ⟨8492430629786239973123959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11323240839714986630831945 8492430629786239973123959)
              ·
                refine ⟨12738645944679359959685939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8492430629786239973123959 12738645944679359959685939)
                ·
                  refine ⟨19107968917019039939528909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12738645944679359959685939 19107968917019039939528909)
                  ·
                    refine ⟨7165488343882139977323341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19107968917019039939528909 7165488343882139977323341)
                    ·
                      refine ⟨2687058128955802491496253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7165488343882139977323341 2687058128955802491496253)
                      ·
                        rfl

theorem cell23_5233027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_5233027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233027 prefixEnd_5233027 := by exact prefixLift 5233027
  have htrace : WordTrace (prefixWord ++ tailWord_5233027) baseStart_5233027 baseEnd_5233027 := by
    simpa [prefixWord, tailWord_5233027, baseEnd_5233027] using wordTrace_append hprefix tailTrace_5233027
  have hstable : (prefixWord ++ tailWord_5233027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233027).length < 2 ^ (prefixWord ++ tailWord_5233027).sum := by decide
  have hdescent : baseEnd_5233027 < baseStart_5233027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233084 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_5233084 : Nat := 118140960795 + 5233084 * 2 ^ 59
def prefixEnd_5233084 : Nat := 4983230072969 + 3 ^ 40 * 5233084 * 2
def baseEnd_5233084 : Nat := 2687087397353108768483491

theorem tailTrace_5233084 : CollatzResearch.WordTrace tailWord_5233084 prefixEnd_5233084 2687087397353108768483491 := by
  unfold tailWord_5233084
  simp only [CollatzResearch.WordTrace]
  refine ⟨95433126886718941219033153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127244169182291921625377537 95433126886718941219033153)
  ·
    refine ⟨71574845165039205914274865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95433126886718941219033153 71574845165039205914274865)
    ·
      refine ⟨53681133873779404435706149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71574845165039205914274865 53681133873779404435706149)
      ·
        refine ⟨10065212601333638331694903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53681133873779404435706149 10065212601333638331694903)
        ·
          refine ⟨15097818902000457497542355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10065212601333638331694903 15097818902000457497542355)
          ·
            refine ⟨22646728353000686246313533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15097818902000457497542355 22646728353000686246313533)
            ·
              refine ⟨8492523132375257342367575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22646728353000686246313533 8492523132375257342367575)
              ·
                refine ⟨12738784698562886013551363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8492523132375257342367575 12738784698562886013551363)
                ·
                  refine ⟨19108177047844329020327045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12738784698562886013551363 19108177047844329020327045)
                  ·
                    refine ⟨3582783196470811691311321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19108177047844329020327045 3582783196470811691311321)
                    ·
                      refine ⟨2687087397353108768483491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582783196470811691311321 2687087397353108768483491)
                      ·
                        rfl

theorem cell23_5233084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_5233084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233084 prefixEnd_5233084 := by exact prefixLift 5233084
  have htrace : WordTrace (prefixWord ++ tailWord_5233084) baseStart_5233084 baseEnd_5233084 := by
    simpa [prefixWord, tailWord_5233084, baseEnd_5233084] using wordTrace_append hprefix tailTrace_5233084
  have hstable : (prefixWord ++ tailWord_5233084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233084).length < 2 ^ (prefixWord ++ tailWord_5233084).sum := by decide
  have hdescent : baseEnd_5233084 < baseStart_5233084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233120 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 2, 5]
def baseStart_5233120 : Nat := 118140960795 + 5233120 * 2 ^ 59
def prefixEnd_5233120 : Nat := 4983230072969 + 3 ^ 40 * 5233120 * 2
def baseEnd_5233120 : Nat := 895701960885556875877775

theorem tailTrace_5233120 : CollatzResearch.WordTrace tailWord_5233120 prefixEnd_5233120 895701960885556875877775 := by
  unfold tailWord_5233120
  simp only [CollatzResearch.WordTrace]
  refine ⟨95433783400653730293188407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127245044534204973724251209 95433783400653730293188407)
  ·
    refine ⟨143150675100980595439782611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95433783400653730293188407 143150675100980595439782611)
    ·
      refine ⟨214726012651470893159673917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143150675100980595439782611 214726012651470893159673917)
      ·
        refine ⟨80522254744301584934877719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214726012651470893159673917 80522254744301584934877719)
        ·
          refine ⟨120783382116452377402316579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80522254744301584934877719 120783382116452377402316579)
          ·
            refine ⟨181175073174678566103474869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120783382116452377402316579 181175073174678566103474869)
            ·
              refine ⟨16985163110126115572200769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181175073174678566103474869 16985163110126115572200769)
              ·
                refine ⟨12738872332594586679150577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16985163110126115572200769 12738872332594586679150577)
                ·
                  refine ⟨9554154249445940009362933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12738872332594586679150577 9554154249445940009362933)
                  ·
                    refine ⟨895701960885556875877775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9554154249445940009362933 895701960885556875877775)
                    ·
                      rfl

theorem cell23_5233120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_5233120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233120 prefixEnd_5233120 := by exact prefixLift 5233120
  have htrace : WordTrace (prefixWord ++ tailWord_5233120) baseStart_5233120 baseEnd_5233120 := by
    simpa [prefixWord, tailWord_5233120, baseEnd_5233120] using wordTrace_append hprefix tailTrace_5233120
  have hstable : (prefixWord ++ tailWord_5233120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233120).length < 2 ^ (prefixWord ++ tailWord_5233120).sum := by decide
  have hdescent : baseEnd_5233120 < baseStart_5233120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233127 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_5233127 : Nat := 118140960795 + 5233127 * 2 ^ 59
def prefixEnd_5233127 : Nat := 4983230072969 + 3 ^ 40 * 5233127 * 2
def baseEnd_5233127 : Nat := 2687109477021252100245793

theorem tailTrace_5233127 : CollatzResearch.WordTrace tailWord_5233127 prefixEnd_5233127 2687109477021252100245793 := by
  unfold tailWord_5233127
  simp only [CollatzResearch.WordTrace]
  refine ⟨190867822112282100781881635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127245214741521400521254423 190867822112282100781881635)
  ·
    refine ⟨286301733168423151172822453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190867822112282100781881635 286301733168423151172822453)
    ·
      refine ⟨26840787484539670422452105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 286301733168423151172822453 26840787484539670422452105)
      ·
        refine ⟨20130590613404752816839079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26840787484539670422452105 20130590613404752816839079)
        ·
          refine ⟨30195885920107129225258619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20130590613404752816839079 30195885920107129225258619)
          ·
            refine ⟨45293828880160693837887929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30195885920107129225258619 45293828880160693837887929)
            ·
              refine ⟨33970371660120520378415947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45293828880160693837887929 33970371660120520378415947)
              ·
                refine ⟨50955557490180780567623921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33970371660120520378415947 50955557490180780567623921)
                ·
                  refine ⟨38216668117635585425717941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50955557490180780567623921 38216668117635585425717941)
                  ·
                    refine ⟨3582812636028336133661057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38216668117635585425717941 3582812636028336133661057)
                    ·
                      refine ⟨2687109477021252100245793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582812636028336133661057 2687109477021252100245793)
                      ·
                        rfl

theorem cell23_5233127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_5233127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233127 prefixEnd_5233127 := by exact prefixLift 5233127
  have htrace : WordTrace (prefixWord ++ tailWord_5233127) baseStart_5233127 baseEnd_5233127 := by
    simpa [prefixWord, tailWord_5233127, baseEnd_5233127] using wordTrace_append hprefix tailTrace_5233127
  have hstable : (prefixWord ++ tailWord_5233127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233127).length < 2 ^ (prefixWord ++ tailWord_5233127).sum := by decide
  have hdescent : baseEnd_5233127 < baseStart_5233127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233130 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_5233130 : Nat := 118140960795 + 5233130 * 2 ^ 59
def prefixEnd_5233130 : Nat := 4983230072969 + 3 ^ 40 * 5233130 * 2
def baseEnd_5233130 : Nat := 2687111017463215588508279

theorem tailTrace_5233130 : CollatzResearch.WordTrace tailWord_5233130 prefixEnd_5233130 2687111017463215588508279 := by
  unfold tailWord_5233130
  simp only [CollatzResearch.WordTrace]
  refine ⟨47716982882817808073560211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127245287687514154862827229 47716982882817808073560211)
  ·
    refine ⟨71575474324226712110340317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47716982882817808073560211 71575474324226712110340317)
    ·
      refine ⟨26840802871585017041377619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71575474324226712110340317 26840802871585017041377619)
      ·
        refine ⟨40261204307377525562066429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26840802871585017041377619 40261204307377525562066429)
        ·
          refine ⟨15097951615266572085774911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40261204307377525562066429 15097951615266572085774911)
          ·
            refine ⟨22646927422899858128662367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15097951615266572085774911 22646927422899858128662367)
            ·
              refine ⟨33970391134349787192993551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22646927422899858128662367 33970391134349787192993551)
              ·
                refine ⟨50955586701524680789490327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33970391134349787192993551 50955586701524680789490327)
                ·
                  refine ⟨76433380052287021184235491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50955586701524680789490327 76433380052287021184235491)
                  ·
                    refine ⟨114650070078430531776353237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76433380052287021184235491 114650070078430531776353237)
                    ·
                      refine ⟨2687111017463215588508279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114650070078430531776353237 2687111017463215588508279)
                      ·
                        rfl

theorem cell23_5233130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_5233130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233130 prefixEnd_5233130 := by exact prefixLift 5233130
  have htrace : WordTrace (prefixWord ++ tailWord_5233130) baseStart_5233130 baseEnd_5233130 := by
    simpa [prefixWord, tailWord_5233130, baseEnd_5233130] using wordTrace_append hprefix tailTrace_5233130
  have hstable : (prefixWord ++ tailWord_5233130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233130).length < 2 ^ (prefixWord ++ tailWord_5233130).sum := by decide
  have hdescent : baseEnd_5233130 < baseStart_5233130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233143 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_5233143 : Nat := 118140960795 + 5233143 * 2 ^ 59
def prefixEnd_5233143 : Nat := 4983230072969 + 3 ^ 40 * 5233143 * 2
def baseEnd_5233143 : Nat := 2687117692711724037645719

theorem tailTrace_5233143 : CollatzResearch.WordTrace tailWord_5233143 prefixEnd_5233143 2687117692711724037645719 := by
  unfold tailWord_5233143
  simp only [CollatzResearch.WordTrace]
  refine ⟨190868405680224135514464083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127245603786816090342976055 190868405680224135514464083)
  ·
    refine ⟨286302608520336203271696125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190868405680224135514464083 286302608520336203271696125)
    ·
      refine ⟨107363478195126076226886047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286302608520336203271696125 107363478195126076226886047)
      ·
        refine ⟨161045217292689114340329071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107363478195126076226886047 161045217292689114340329071)
        ·
          refine ⟨241567825939033671510493607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161045217292689114340329071 241567825939033671510493607)
          ·
            refine ⟨362351738908550507265740411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241567825939033671510493607 362351738908550507265740411)
            ·
              refine ⟨543527608362825760898610617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362351738908550507265740411 543527608362825760898610617)
              ·
                refine ⟨407645706272119320673957963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543527608362825760898610617 407645706272119320673957963)
                ·
                  refine ⟨611468559408178981010936945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407645706272119320673957963 611468559408178981010936945)
                  ·
                    refine ⟨458601419556134235758202709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 611468559408178981010936945 458601419556134235758202709)
                    ·
                      refine ⟨2687117692711724037645719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 458601419556134235758202709 2687117692711724037645719)
                      ·
                        rfl

theorem cell23_5233143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_5233143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233143 prefixEnd_5233143 := by exact prefixLift 5233143
  have htrace : WordTrace (prefixWord ++ tailWord_5233143) baseStart_5233143 baseEnd_5233143 := by
    simpa [prefixWord, tailWord_5233143, baseEnd_5233143] using wordTrace_append hprefix tailTrace_5233143
  have hstable : (prefixWord ++ tailWord_5233143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233143).length < 2 ^ (prefixWord ++ tailWord_5233143).sum := by decide
  have hdescent : baseEnd_5233143 < baseStart_5233143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233234 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_5233234 : Nat := 118140960795 + 5233234 * 2 ^ 59
def prefixEnd_5233234 : Nat := 4983230072969 + 3 ^ 40 * 5233234 * 2
def baseEnd_5233234 : Nat := 2687164419451283181607801

theorem tailTrace_5233234 : CollatzResearch.WordTrace tailWord_5233234 prefixEnd_5233234 2687164419451283181607801 := by
  unfold tailWord_5233234
  simp only [CollatzResearch.WordTrace]
  refine ⟨47717931180723614514006689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127247816481929638704017837 47717931180723614514006689)
  ·
    refine ⟨35788448385542710885505017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47717931180723614514006689 35788448385542710885505017)
    ·
      refine ⟨26841336289157033164128763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35788448385542710885505017 26841336289157033164128763)
      ·
        refine ⟨40262004433735549746193145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26841336289157033164128763 40262004433735549746193145)
        ·
          refine ⟨30196503325301662309644859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40262004433735549746193145 30196503325301662309644859)
          ·
            refine ⟨45294754987952493464467289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30196503325301662309644859 45294754987952493464467289)
            ·
              refine ⟨33971066240964370098350467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45294754987952493464467289 33971066240964370098350467)
              ·
                refine ⟨50956599361446555147525701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33971066240964370098350467 50956599361446555147525701)
                ·
                  refine ⟨9554362380271229090161069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50956599361446555147525701 9554362380271229090161069)
                  ·
                    refine ⟨3582885892601710908810401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9554362380271229090161069 3582885892601710908810401)
                    ·
                      refine ⟨2687164419451283181607801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582885892601710908810401 2687164419451283181607801)
                      ·
                        rfl

theorem cell23_5233234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_5233234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233234 prefixEnd_5233234 := by exact prefixLift 5233234
  have htrace : WordTrace (prefixWord ++ tailWord_5233234) baseStart_5233234 baseEnd_5233234 := by
    simpa [prefixWord, tailWord_5233234, baseEnd_5233234] using wordTrace_append hprefix tailTrace_5233234
  have hstable : (prefixWord ++ tailWord_5233234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233234).length < 2 ^ (prefixWord ++ tailWord_5233234).sum := by decide
  have hdescent : baseEnd_5233234 < baseStart_5233234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233240 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 3, 6]
def baseStart_5233240 : Nat := 118140960795 + 5233240 * 2 ^ 59
def prefixEnd_5233240 : Nat := 4983230072969 + 3 ^ 40 * 5233240 * 2
def baseEnd_5233240 : Nat := 895722500111736719377591

theorem tailTrace_5233240 : CollatzResearch.WordTrace tailWord_5233240 prefixEnd_5233240 895722500111736719377591 := by
  unfold tailWord_5233240
  simp only [CollatzResearch.WordTrace]
  refine ⟨95435971780436360540372587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127247962373915147387163449 95435971780436360540372587)
  ·
    refine ⟨143153957670654540810558881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95435971780436360540372587 143153957670654540810558881)
    ·
      refine ⟨107365468252990905607919161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143153957670654540810558881 107365468252990905607919161)
      ·
        refine ⟨80524101189743179205939371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107365468252990905607919161 80524101189743179205939371)
        ·
          refine ⟨120786151784614768808909057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80524101189743179205939371 120786151784614768808909057)
          ·
            refine ⟨90589613838461076606681793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120786151784614768808909057 90589613838461076606681793)
            ·
              refine ⟨67942210378845807455011345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90589613838461076606681793 67942210378845807455011345)
              ·
                refine ⟨50956657784134355591258509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67942210378845807455011345 50956657784134355591258509)
                ·
                  refine ⟨19108746669050383346721941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50956657784134355591258509 19108746669050383346721941)
                  ·
                    refine ⟨895722500111736719377591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19108746669050383346721941 895722500111736719377591)
                    ·
                      rfl

theorem cell23_5233240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_5233240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233240 prefixEnd_5233240 := by exact prefixLift 5233240
  have htrace : WordTrace (prefixWord ++ tailWord_5233240) baseStart_5233240 baseEnd_5233240 := by
    simpa [prefixWord, tailWord_5233240, baseEnd_5233240] using wordTrace_append hprefix tailTrace_5233240
  have hstable : (prefixWord ++ tailWord_5233240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233240).length < 2 ^ (prefixWord ++ tailWord_5233240).sum := by decide
  have hdescent : baseEnd_5233240 < baseStart_5233240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233284 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_5233284 : Nat := 118140960795 + 5233284 * 2 ^ 59
def prefixEnd_5233284 : Nat := 4983230072969 + 3 ^ 40 * 5233284 * 2
def baseEnd_5233284 : Nat := 2687190093484007985982571

theorem tailTrace_5233284 : CollatzResearch.WordTrace tailWord_5233284 prefixEnd_5233284 2687190093484007985982571 := by
  unfold tailWord_5233284
  simp only [CollatzResearch.WordTrace]
  refine ⟨95436774186356658297673453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127249032248475544396897937 95436774186356658297673453)
  ·
    refine ⟨35788790319883746861627545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95436774186356658297673453 35788790319883746861627545)
    ·
      refine ⟨26841592739912810146220659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35788790319883746861627545 26841592739912810146220659)
      ·
        refine ⟨40262389109869215219330989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26841592739912810146220659 40262389109869215219330989)
        ·
          refine ⟨15098395916200955707249121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40262389109869215219330989 15098395916200955707249121)
          ·
            refine ⟨11323796937150716780436841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15098395916200955707249121 11323796937150716780436841)
            ·
              refine ⟨8492847702863037585327631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11323796937150716780436841 8492847702863037585327631)
              ·
                refine ⟨12739271554294556377991447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8492847702863037585327631 12739271554294556377991447)
                ·
                  refine ⟨19108907331441834566987171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12739271554294556377991447 19108907331441834566987171)
                  ·
                    refine ⟨28663360997162751850480757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19108907331441834566987171 28663360997162751850480757)
                    ·
                      refine ⟨2687190093484007985982571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28663360997162751850480757 2687190093484007985982571)
                      ·
                        rfl

theorem cell23_5233284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_5233284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233284 prefixEnd_5233284 := by exact prefixLift 5233284
  have htrace : WordTrace (prefixWord ++ tailWord_5233284) baseStart_5233284 baseEnd_5233284 := by
    simpa [prefixWord, tailWord_5233284, baseEnd_5233284] using wordTrace_append hprefix tailTrace_5233284
  have hstable : (prefixWord ++ tailWord_5233284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233284).length < 2 ^ (prefixWord ++ tailWord_5233284).sum := by decide
  have hdescent : baseEnd_5233284 < baseStart_5233284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233298 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_5233298 : Nat := 118140960795 + 5233298 * 2 ^ 59
def prefixEnd_5233298 : Nat := 4983230072969 + 3 ^ 40 * 5233298 * 2
def baseEnd_5233298 : Nat := 2687197282213170931207507

theorem tailTrace_5233298 : CollatzResearch.WordTrace tailWord_5233298 prefixEnd_5233298 2687197282213170931207507 := by
  unfold tailWord_5233298
  simp only [CollatzResearch.WordTrace]
  refine ⟨47718514748665649246589137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127249372663108397990904365 47718514748665649246589137)
  ·
    refine ⟨35788886061499236934941853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47718514748665649246589137 35788886061499236934941853)
    ·
      refine ⟨13420832273062213850603195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35788886061499236934941853 13420832273062213850603195)
      ·
        refine ⟨20131248409593320775904793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13420832273062213850603195 20131248409593320775904793)
        ·
          refine ⟨15098436307194990581928595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20131248409593320775904793 15098436307194990581928595)
          ·
            refine ⟨22647654460792485872892893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15098436307194990581928595 22647654460792485872892893)
            ·
              refine ⟨8492870422797182202334835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22647654460792485872892893 8492870422797182202334835)
              ·
                refine ⟨12739305634195773303502253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8492870422797182202334835 12739305634195773303502253)
                ·
                  refine ⟨4777239612823414988813345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12739305634195773303502253 4777239612823414988813345)
                  ·
                    refine ⟨3582929709617561241610009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4777239612823414988813345 3582929709617561241610009)
                    ·
                      refine ⟨2687197282213170931207507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3582929709617561241610009 2687197282213170931207507)
                      ·
                        rfl

theorem cell23_5233298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_5233298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233298 prefixEnd_5233298 := by exact prefixLift 5233298
  have htrace : WordTrace (prefixWord ++ tailWord_5233298) baseStart_5233298 baseEnd_5233298 := by
    simpa [prefixWord, tailWord_5233298, baseEnd_5233298] using wordTrace_append hprefix tailTrace_5233298
  have hstable : (prefixWord ++ tailWord_5233298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233298).length < 2 ^ (prefixWord ++ tailWord_5233298).sum := by decide
  have hdescent : baseEnd_5233298 < baseStart_5233298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233308 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_5233308 : Nat := 118140960795 + 5233308 * 2 ^ 59
def prefixEnd_5233308 : Nat := 4983230072969 + 3 ^ 40 * 5233308 * 2
def baseEnd_5233308 : Nat := 895734139006571964027487

theorem tailTrace_5233308 : CollatzResearch.WordTrace tailWord_5233308 prefixEnd_5233308 895734139006571964027487 := by
  unfold tailWord_5233308
  simp only [CollatzResearch.WordTrace]
  refine ⟨95437211862313184347110289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127249615816417579129480385 95437211862313184347110289)
  ·
    refine ⟨71577908896734888260332717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95437211862313184347110289 71577908896734888260332717)
    ·
      refine ⟨26841715836275583097624769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71577908896734888260332717 26841715836275583097624769)
      ·
        refine ⟨20131286877206687323218577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26841715836275583097624769 20131286877206687323218577)
        ·
          refine ⟨15098465157905015492413933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20131286877206687323218577 15098465157905015492413933)
          ·
            refine ⟨5661924434214380809655225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15098465157905015492413933 5661924434214380809655225)
            ·
              refine ⟨4246443325660785607241419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5661924434214380809655225 4246443325660785607241419)
              ·
                refine ⟨6369664988491178410862129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4246443325660785607241419 6369664988491178410862129)
                ·
                  refine ⟨4777248741368383808146597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6369664988491178410862129 4777248741368383808146597)
                  ·
                    refine ⟨895734139006571964027487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4777248741368383808146597 895734139006571964027487)
                    ·
                      rfl

theorem cell23_5233308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_5233308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233308 prefixEnd_5233308 := by exact prefixLift 5233308
  have htrace : WordTrace (prefixWord ++ tailWord_5233308) baseStart_5233308 baseEnd_5233308 := by
    simpa [prefixWord, tailWord_5233308, baseEnd_5233308] using wordTrace_append hprefix tailTrace_5233308
  have hstable : (prefixWord ++ tailWord_5233308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233308).length < 2 ^ (prefixWord ++ tailWord_5233308).sum := by decide
  have hdescent : baseEnd_5233308 < baseStart_5233308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233348 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_5233348 : Nat := 118140960795 + 5233348 * 2 ^ 59
def prefixEnd_5233348 : Nat := 4983230072969 + 3 ^ 40 * 5233348 * 2
def baseEnd_5233348 : Nat := 2687222956245895735582277

theorem tailTrace_5233348 : CollatzResearch.WordTrace tailWord_5233348 prefixEnd_5233348 2687222956245895735582277 := by
  unfold tailWord_5233348
  simp only [CollatzResearch.WordTrace]
  refine ⟨95437941322240727762838349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127250588429654303683784465 95437941322240727762838349)
  ·
    refine ⟨35789227995840272911064381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95437941322240727762838349 35789227995840272911064381)
    ·
      refine ⟨13420960498440102341649143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35789227995840272911064381 13420960498440102341649143)
      ·
        refine ⟨20131440747660153512473715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13420960498440102341649143 20131440747660153512473715)
        ·
          refine ⟨30197161121490230268710573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20131440747660153512473715 30197161121490230268710573)
          ·
            refine ⟨11323935420558836350766465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30197161121490230268710573 11323935420558836350766465)
            ·
              refine ⟨8492951565419127263074849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11323935420558836350766465 8492951565419127263074849)
              ·
                refine ⟨6369713674064345447306137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8492951565419127263074849 6369713674064345447306137)
                ·
                  refine ⟨4777285255548259085479603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6369713674064345447306137 4777285255548259085479603)
                  ·
                    refine ⟨7165927883322388628219405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4777285255548259085479603 7165927883322388628219405)
                    ·
                      refine ⟨2687222956245895735582277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7165927883322388628219405 2687222956245895735582277)
                      ·
                        rfl

theorem cell23_5233348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_5233348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233348 prefixEnd_5233348 := by exact prefixLift 5233348
  have htrace : WordTrace (prefixWord ++ tailWord_5233348) baseStart_5233348 baseEnd_5233348 := by
    simpa [prefixWord, tailWord_5233348, baseEnd_5233348] using wordTrace_append hprefix tailTrace_5233348
  have hstable : (prefixWord ++ tailWord_5233348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233348).length < 2 ^ (prefixWord ++ tailWord_5233348).sum := by decide
  have hdescent : baseEnd_5233348 < baseStart_5233348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233367 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_5233367 : Nat := 118140960795 + 5233367 * 2 ^ 59
def prefixEnd_5233367 : Nat := 4983230072969 + 3 ^ 40 * 5233367 * 2
def baseEnd_5233367 : Nat := 2687232712378331161244689

theorem tailTrace_5233367 : CollatzResearch.WordTrace tailWord_5233367 prefixEnd_5233367 2687232712378331161244689 := by
  unfold tailWord_5233367
  simp only [CollatzResearch.WordTrace]
  refine ⟨190876575631412621770618355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127251050420941747847078903 190876575631412621770618355)
  ·
    refine ⟨286314863447118932655927533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190876575631412621770618355 286314863447118932655927533)
    ·
      refine ⟨107368073792669599745972825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286314863447118932655927533 107368073792669599745972825)
      ·
        refine ⟨80526055344502199809479619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107368073792669599745972825 80526055344502199809479619)
        ·
          refine ⟨120789083016753299714219429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80526055344502199809479619 120789083016753299714219429)
          ·
            refine ⟨22647953065641243696416143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120789083016753299714219429 22647953065641243696416143)
            ·
              refine ⟨33971929598461865544624215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22647953065641243696416143 33971929598461865544624215)
              ·
                refine ⟨50957894397692798316936323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33971929598461865544624215 50957894397692798316936323)
                ·
                  refine ⟨76436841596539197475404485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50957894397692798316936323 76436841596539197475404485)
                  ·
                    refine ⟨14331907799351099526638341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76436841596539197475404485 14331907799351099526638341)
                    ·
                      refine ⟨2687232712378331161244689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14331907799351099526638341 2687232712378331161244689)
                      ·
                        rfl

theorem cell23_5233367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_5233367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233367 prefixEnd_5233367 := by exact prefixLift 5233367
  have htrace : WordTrace (prefixWord ++ tailWord_5233367) baseStart_5233367 baseEnd_5233367 := by
    simpa [prefixWord, tailWord_5233367, baseEnd_5233367] using wordTrace_append hprefix tailTrace_5233367
  have hstable : (prefixWord ++ tailWord_5233367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233367).length < 2 ^ (prefixWord ++ tailWord_5233367).sum := by decide
  have hdescent : baseEnd_5233367 < baseStart_5233367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233377 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 9]
def baseStart_5233377 : Nat := 118140960795 + 5233377 * 2 ^ 59
def prefixEnd_5233377 : Nat := 4983230072969 + 3 ^ 40 * 5233377 * 2
def baseEnd_5233377 : Nat := 298581983020541791346627

theorem tailTrace_5233377 : CollatzResearch.WordTrace tailWord_5233377 prefixEnd_5233377 298581983020541791346627 := by
  unfold tailWord_5233377
  simp only [CollatzResearch.WordTrace]
  refine ⟨190876940361376393478482385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127251293574250928985654923 190876940361376393478482385)
  ·
    refine ⟨143157705271032295108861789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190876940361376393478482385 143157705271032295108861789)
    ·
      refine ⟨53684139476637110665823171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143157705271032295108861789 53684139476637110665823171)
      ·
        refine ⟨80526209214955665998734757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53684139476637110665823171 80526209214955665998734757)
        ·
          refine ⟨15098664227804187374762767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80526209214955665998734757 15098664227804187374762767)
          ·
            refine ⟨22647996341706281062144151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15098664227804187374762767 22647996341706281062144151)
            ·
              refine ⟨33971994512559421593216227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22647996341706281062144151 33971994512559421593216227)
              ·
                refine ⟨50957991768839132389824341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33971994512559421593216227 50957991768839132389824341)
                ·
                  refine ⟨298581983020541791346627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50957991768839132389824341 298581983020541791346627)
                  ·
                    rfl

theorem cell23_5233377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 9].length) (baseStart_5233377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233377 prefixEnd_5233377 := by exact prefixLift 5233377
  have htrace : WordTrace (prefixWord ++ tailWord_5233377) baseStart_5233377 baseEnd_5233377 := by
    simpa [prefixWord, tailWord_5233377, baseEnd_5233377] using wordTrace_append hprefix tailTrace_5233377
  have hstable : (prefixWord ++ tailWord_5233377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233377).length < 2 ^ (prefixWord ++ tailWord_5233377).sum := by decide
  have hdescent : baseEnd_5233377 < baseStart_5233377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233387 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 3]
def baseStart_5233387 : Nat := 118140960795 + 5233387 * 2 ^ 59
def prefixEnd_5233387 : Nat := 4983230072969 + 3 ^ 40 * 5233387 * 2
def baseEnd_5233387 : Nat := 2687242981991421082994597

theorem tailTrace_5233387 : CollatzResearch.WordTrace tailWord_5233387 prefixEnd_5233387 2687242981991421082994597 := by
  unfold tailWord_5233387
  simp only [CollatzResearch.WordTrace]
  refine ⟨190877305091340165186346415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127251536727560110124230943 190877305091340165186346415)
  ·
    refine ⟨286315957637010247779519623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190877305091340165186346415 286315957637010247779519623)
    ·
      refine ⟨429473936455515371669279435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286315957637010247779519623 429473936455515371669279435)
      ·
        refine ⟨644210904683273057503919153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429473936455515371669279435 644210904683273057503919153)
        ·
          refine ⟨483158178512454793127939365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644210904683273057503919153 483158178512454793127939365)
          ·
            refine ⟨90592158471085273711488631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 483158178512454793127939365 90592158471085273711488631)
            ·
              refine ⟨135888237706627910567232947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90592158471085273711488631 135888237706627910567232947)
              ·
                refine ⟨203832356559941865850849421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135888237706627910567232947 203832356559941865850849421)
                ·
                  refine ⟨76437133709978199694068533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203832356559941865850849421 76437133709978199694068533)
                  ·
                    refine ⟨7165981285310456221318925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76437133709978199694068533 7165981285310456221318925)
                    ·
                      refine ⟨2687242981991421082994597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7165981285310456221318925 2687242981991421082994597)
                      ·
                        rfl

theorem cell23_5233387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 3].length) (baseStart_5233387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233387 prefixEnd_5233387 := by exact prefixLift 5233387
  have htrace : WordTrace (prefixWord ++ tailWord_5233387) baseStart_5233387 baseEnd_5233387 := by
    simpa [prefixWord, tailWord_5233387, baseEnd_5233387] using wordTrace_append hprefix tailTrace_5233387
  have hstable : (prefixWord ++ tailWord_5233387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233387).length < 2 ^ (prefixWord ++ tailWord_5233387).sum := by decide
  have hdescent : baseEnd_5233387 < baseStart_5233387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233404 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_5233404 : Nat := 118140960795 + 5233404 * 2 ^ 59
def prefixEnd_5233404 : Nat := 4983230072969 + 3 ^ 40 * 5233404 * 2
def baseEnd_5233404 : Nat := 2687251711162547516482019

theorem tailTrace_5233404 : CollatzResearch.WordTrace tailWord_5233404 prefixEnd_5233404 2687251711162547516482019 := by
  unfold tailWord_5233404
  simp only [CollatzResearch.WordTrace]
  refine ⟨95438962566139288544857633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127251950088185718059810177 95438962566139288544857633)
  ·
    refine ⟨71579221924604466408643225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95438962566139288544857633 71579221924604466408643225)
    ·
      refine ⟨53684416443453349806482419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71579221924604466408643225 53684416443453349806482419)
      ·
        refine ⟨80526624665180024709723629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53684416443453349806482419 80526624665180024709723629)
        ·
          refine ⟨30197484249442509266146361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80526624665180024709723629 30197484249442509266146361)
          ·
            refine ⟨22648113187081881949609771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30197484249442509266146361 22648113187081881949609771)
            ·
              refine ⟨33972169780622822924414657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22648113187081881949609771 33972169780622822924414657)
              ·
                refine ⟨25479127335467117193310993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33972169780622822924414657 25479127335467117193310993)
                ·
                  refine ⟨19109345501600337894983245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25479127335467117193310993 19109345501600337894983245)
                  ·
                    refine ⟨7166004563100126710618717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19109345501600337894983245 7166004563100126710618717)
                    ·
                      refine ⟨2687251711162547516482019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7166004563100126710618717 2687251711162547516482019)
                      ·
                        rfl

theorem cell23_5233404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_5233404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233404 prefixEnd_5233404 := by exact prefixLift 5233404
  have htrace : WordTrace (prefixWord ++ tailWord_5233404) baseStart_5233404 baseEnd_5233404 := by
    simpa [prefixWord, tailWord_5233404, baseEnd_5233404] using wordTrace_append hprefix tailTrace_5233404
  have hstable : (prefixWord ++ tailWord_5233404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233404).length < 2 ^ (prefixWord ++ tailWord_5233404).sum := by decide
  have hdescent : baseEnd_5233404 < baseStart_5233404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233407 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 4, 5]
def baseStart_5233407 : Nat := 118140960795 + 5233407 * 2 ^ 59
def prefixEnd_5233407 : Nat := 4983230072969 + 3 ^ 40 * 5233407 * 2
def baseEnd_5233407 : Nat := 895751083868170334914835

theorem tailTrace_5233407 : CollatzResearch.WordTrace tailWord_5233407 prefixEnd_5233407 895751083868170334914835 := by
  unfold tailWord_5233407
  simp only [CollatzResearch.WordTrace]
  refine ⟨190878034551267708602074475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127252023034178472401382983 190878034551267708602074475)
  ·
    refine ⟨286317051826901562903111713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190878034551267708602074475 286317051826901562903111713)
    ·
      refine ⟨214737788870176172177333785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286317051826901562903111713 214737788870176172177333785)
      ·
        refine ⟨161053341652632129133000339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214737788870176172177333785 161053341652632129133000339)
        ·
          refine ⟨241580012478948193699500509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161053341652632129133000339 241580012478948193699500509)
          ·
            refine ⟨90592504679605572637312691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241580012478948193699500509 90592504679605572637312691)
            ·
              refine ⟨135888757019408358955969037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90592504679605572637312691 135888757019408358955969037)
              ·
                refine ⟨50958283882278134608488389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135888757019408358955969037 50958283882278134608488389)
                ·
                  refine ⟨9554678227927150239091573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50958283882278134608488389 9554678227927150239091573)
                  ·
                    refine ⟨895751083868170334914835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9554678227927150239091573 895751083868170334914835)
                    ·
                      rfl

theorem cell23_5233407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_5233407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233407 prefixEnd_5233407 := by exact prefixLift 5233407
  have htrace : WordTrace (prefixWord ++ tailWord_5233407) baseStart_5233407 baseEnd_5233407 := by
    simpa [prefixWord, tailWord_5233407, baseEnd_5233407] using wordTrace_append hprefix tailTrace_5233407
  have hstable : (prefixWord ++ tailWord_5233407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233407).length < 2 ^ (prefixWord ++ tailWord_5233407).sum := by decide
  have hdescent : baseEnd_5233407 < baseStart_5233407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233417 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_5233417 : Nat := 118140960795 + 5233417 * 2 ^ 59
def prefixEnd_5233417 : Nat := 4983230072969 + 3 ^ 40 * 5233417 * 2
def baseEnd_5233417 : Nat := 2687258386411055965619459

theorem tailTrace_5233417 : CollatzResearch.WordTrace tailWord_5233417 prefixEnd_5233417 2687258386411055965619459 := by
  unfold tailWord_5233417
  simp only [CollatzResearch.WordTrace]
  refine ⟨190878399281231480309938505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127252266187487653539959003 190878399281231480309938505)
  ·
    refine ⟨143158799460923610232453879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190878399281231480309938505 143158799460923610232453879)
    ·
      refine ⟨214738199191385415348680819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143158799460923610232453879 214738199191385415348680819)
      ·
        refine ⟨322107298787078123023021229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214738199191385415348680819 322107298787078123023021229)
        ·
          refine ⟨120790237045154296133632961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322107298787078123023021229 120790237045154296133632961)
          ·
            refine ⟨90592677783865722100224721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120790237045154296133632961 90592677783865722100224721)
            ·
              refine ⟨67944508337899291575168541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90592677783865722100224721 67944508337899291575168541)
              ·
                refine ⟨25479190626712234340688203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67944508337899291575168541 25479190626712234340688203)
                ·
                  refine ⟨38218785940068351511032305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25479190626712234340688203 38218785940068351511032305)
                  ·
                    refine ⟨28664089455051263633274229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38218785940068351511032305 28664089455051263633274229)
                    ·
                      refine ⟨2687258386411055965619459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28664089455051263633274229 2687258386411055965619459)
                      ·
                        rfl

theorem cell23_5233417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_5233417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233417 prefixEnd_5233417 := by exact prefixLift 5233417
  have htrace : WordTrace (prefixWord ++ tailWord_5233417) baseStart_5233417 baseEnd_5233417 := by
    simpa [prefixWord, tailWord_5233417, baseEnd_5233417] using wordTrace_append hprefix tailTrace_5233417
  have hstable : (prefixWord ++ tailWord_5233417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233417).length < 2 ^ (prefixWord ++ tailWord_5233417).sum := by decide
  have hdescent : baseEnd_5233417 < baseStart_5233417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233427 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 4]
def baseStart_5233427 : Nat := 118140960795 + 5233427 * 2 ^ 59
def prefixEnd_5233427 : Nat := 4983230072969 + 3 ^ 40 * 5233427 * 2
def baseEnd_5233427 : Nat := 2687263521217600926494413

theorem tailTrace_5233427 : CollatzResearch.WordTrace tailWord_5233427 prefixEnd_5233427 2687263521217600926494413 := by
  unfold tailWord_5233427
  simp only [CollatzResearch.WordTrace]
  refine ⟨190878764011195252017802535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127252509340796834678535023 190878764011195252017802535)
  ·
    refine ⟨286318146016792878026703803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190878764011195252017802535 286318146016792878026703803)
    ·
      refine ⟨429477219025189317040055705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286318146016792878026703803 429477219025189317040055705)
      ·
        refine ⟨322107914268891987780041779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429477219025189317040055705 322107914268891987780041779)
        ·
          refine ⟨483161871403337981670062669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322107914268891987780041779 483161871403337981670062669)
          ·
            refine ⟨181185701776251743126273501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 483161871403337981670062669 181185701776251743126273501)
            ·
              refine ⟨67944638166094403672352563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181185701776251743126273501 67944638166094403672352563)
              ·
                refine ⟨101916957249141605508528845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67944638166094403672352563 101916957249141605508528845)
                ·
                  refine ⟨38218858968428102065698317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101916957249141605508528845 38218858968428102065698317)
                  ·
                    refine ⟨14332072113160538274636869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38218858968428102065698317 14332072113160538274636869)
                    ·
                      refine ⟨2687263521217600926494413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14332072113160538274636869 2687263521217600926494413)
                      ·
                        rfl

theorem cell23_5233427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_5233427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233427 prefixEnd_5233427 := by exact prefixLift 5233427
  have htrace : WordTrace (prefixWord ++ tailWord_5233427) baseStart_5233427 baseEnd_5233427 := by
    simpa [prefixWord, tailWord_5233427, baseEnd_5233427] using wordTrace_append hprefix tailTrace_5233427
  have hstable : (prefixWord ++ tailWord_5233427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233427).length < 2 ^ (prefixWord ++ tailWord_5233427).sum := by decide
  have hdescent : baseEnd_5233427 < baseStart_5233427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233461 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_5233461 : Nat := 118140960795 + 5233461 * 2 ^ 59
def prefixEnd_5233461 : Nat := 4983230072969 + 3 ^ 40 * 5233461 * 2
def baseEnd_5233461 : Nat := 2687280979559853793469257

theorem tailTrace_5233461 : CollatzResearch.WordTrace tailWord_5233461 prefixEnd_5233461 2687280979559853793469257 := by
  unfold tailWord_5233461
  simp only [CollatzResearch.WordTrace]
  refine ⟨190880004093072075824540237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127253336062048050549693491 190880004093072075824540237)
  ·
    refine ⟨71580001534902028434202589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190880004093072075824540237 71580001534902028434202589)
    ·
      refine ⟨26842500575588260662825971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71580001534902028434202589 26842500575588260662825971)
      ·
        refine ⟨40263750863382390994238957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26842500575588260662825971 40263750863382390994238957)
        ·
          refine ⟨15098906573768396622839609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40263750863382390994238957 15098906573768396622839609)
          ·
            refine ⟨11324179930326297467129707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15098906573768396622839609 11324179930326297467129707)
            ·
              refine ⟨16986269895489446200694561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11324179930326297467129707 16986269895489446200694561)
              ·
                refine ⟨12739702421617084650520921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16986269895489446200694561 12739702421617084650520921)
                ·
                  refine ⟨9554776816212813487890691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12739702421617084650520921 9554776816212813487890691)
                  ·
                    refine ⟨14332165224319220231836037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9554776816212813487890691 14332165224319220231836037)
                    ·
                      refine ⟨2687280979559853793469257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14332165224319220231836037 2687280979559853793469257)
                      ·
                        rfl

theorem cell23_5233461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_5233461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233461 prefixEnd_5233461 := by exact prefixLift 5233461
  have htrace : WordTrace (prefixWord ++ tailWord_5233461) baseStart_5233461 baseEnd_5233461 := by
    simpa [prefixWord, tailWord_5233461, baseEnd_5233461] using wordTrace_append hprefix tailTrace_5233461
  have hstable : (prefixWord ++ tailWord_5233461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233461).length < 2 ^ (prefixWord ++ tailWord_5233461).sum := by decide
  have hdescent : baseEnd_5233461 < baseStart_5233461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233471 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 3, 4]
def baseStart_5233471 : Nat := 118140960795 + 5233471 * 2 ^ 59
def prefixEnd_5233471 : Nat := 4983230072969 + 3 ^ 40 * 5233471 * 2
def baseEnd_5233471 : Nat := 895762038122132918114737

theorem tailTrace_5233471 : CollatzResearch.WordTrace tailWord_5233471 prefixEnd_5233471 895762038122132918114737 := by
  unfold tailWord_5233471
  simp only [CollatzResearch.WordTrace]
  refine ⟨190880368823035847532404267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127253579215357231688269511 190880368823035847532404267)
  ·
    refine ⟨286320553234553771298606401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190880368823035847532404267 286320553234553771298606401)
    ·
      refine ⟨214740414925915328473954801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286320553234553771298606401 214740414925915328473954801)
      ·
        refine ⟨161055311194436496355466101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214740414925915328473954801 161055311194436496355466101)
        ·
          refine ⟨15098935424478421533324947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161055311194436496355466101 15098935424478421533324947)
          ·
            refine ⟨22648403136717632299987421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15098935424478421533324947 22648403136717632299987421)
            ·
              refine ⟨8493151176269112112495283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22648403136717632299987421 8493151176269112112495283)
              ·
                refine ⟨12739726764403668168742925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8493151176269112112495283 12739726764403668168742925)
                ·
                  refine ⟨4777397536651375563278597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12739726764403668168742925 4777397536651375563278597)
                  ·
                    refine ⟨895762038122132918114737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4777397536651375563278597 895762038122132918114737)
                    ·
                      rfl

theorem cell23_5233471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 4].length) (baseStart_5233471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233471 prefixEnd_5233471 := by exact prefixLift 5233471
  have htrace : WordTrace (prefixWord ++ tailWord_5233471) baseStart_5233471 baseEnd_5233471 := by
    simpa [prefixWord, tailWord_5233471, baseEnd_5233471] using wordTrace_append hprefix tailTrace_5233471
  have hstable : (prefixWord ++ tailWord_5233471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233471).length < 2 ^ (prefixWord ++ tailWord_5233471).sum := by decide
  have hdescent : baseEnd_5233471 < baseStart_5233471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233518 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_5233518 : Nat := 118140960795 + 5233518 * 2 ^ 59
def prefixEnd_5233518 : Nat := 4983230072969 + 3 ^ 40 * 5233518 * 2
def baseEnd_5233518 : Nat := 298590027550795563384055

theorem tailTrace_5233518 : CollatzResearch.WordTrace tailWord_5233518 prefixEnd_5233518 298590027550795563384055 := by
  unfold tailWord_5233518
  simp only [CollatzResearch.WordTrace]
  refine ⟨23860260381733196819920651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127254722035910383039576805 23860260381733196819920651)
  ·
    refine ⟨35790390572599795229880977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23860260381733196819920651 35790390572599795229880977)
    ·
      refine ⟨26842792929449846422410733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35790390572599795229880977 26842792929449846422410733)
      ·
        refine ⟨10066047348543692408404025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26842792929449846422410733 10066047348543692408404025)
        ·
          refine ⟨7549535511407769306303019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10066047348543692408404025 7549535511407769306303019)
          ·
            refine ⟨11324303267111653959454529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7549535511407769306303019 11324303267111653959454529)
            ·
              refine ⟨8493227450333740469590897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11324303267111653959454529 8493227450333740469590897)
              ·
                refine ⟨6369920587750305352193173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8493227450333740469590897 6369920587750305352193173)
                ·
                  refine ⟨298590027550795563384055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6369920587750305352193173 298590027550795563384055)
                  ·
                    rfl

theorem cell23_5233518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_5233518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233518 prefixEnd_5233518 := by exact prefixLift 5233518
  have htrace : WordTrace (prefixWord ++ tailWord_5233518) baseStart_5233518 baseEnd_5233518 := by
    simpa [prefixWord, tailWord_5233518, baseEnd_5233518] using wordTrace_append hprefix tailTrace_5233518
  have hstable : (prefixWord ++ tailWord_5233518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233518).length < 2 ^ (prefixWord ++ tailWord_5233518).sum := by decide
  have hdescent : baseEnd_5233518 < baseStart_5233518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233562 : List Nat := [3, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3]
def baseStart_5233562 : Nat := 118140960795 + 5233562 * 2 ^ 59
def prefixEnd_5233562 : Nat := 4983230072969 + 3 ^ 40 * 5233562 * 2
def baseEnd_5233562 : Nat := 2687332841105957898306293

theorem tailTrace_5233562 : CollatzResearch.WordTrace tailWord_5233562 prefixEnd_5233562 2687332841105957898306293 := by
  unfold tailWord_5233562
  simp only [CollatzResearch.WordTrace]
  refine ⟨47720921966426542518491735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127255791910470780049311293 47720921966426542518491735)
  ·
    refine ⟨71581382949639813777737603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47720921966426542518491735 71581382949639813777737603)
    ·
      refine ⟨107372074424459720666606405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71581382949639813777737603 107372074424459720666606405)
      ·
        refine ⟨20132263954586197624988701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107372074424459720666606405 20132263954586197624988701)
        ·
          refine ⟨7549598982969824109370763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20132263954586197624988701 7549598982969824109370763)
          ·
            refine ⟨11324398474454736164056145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7549598982969824109370763 11324398474454736164056145)
            ·
              refine ⟨8493298855841052123042109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11324398474454736164056145 8493298855841052123042109)
              ·
                refine ⟨3184987070940394546140791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8493298855841052123042109 3184987070940394546140791)
                ·
                  refine ⟨4777480606410591819211187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3184987070940394546140791 4777480606410591819211187)
                  ·
                    refine ⟨7166220909615887728816781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4777480606410591819211187 7166220909615887728816781)
                    ·
                      refine ⟨2687332841105957898306293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7166220909615887728816781 2687332841105957898306293)
                      ·
                        rfl

theorem cell23_5233562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_5233562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233562 prefixEnd_5233562 := by exact prefixLift 5233562
  have htrace : WordTrace (prefixWord ++ tailWord_5233562) baseStart_5233562 baseEnd_5233562 := by
    simpa [prefixWord, tailWord_5233562, baseEnd_5233562] using wordTrace_append hprefix tailTrace_5233562
  have hstable : (prefixWord ++ tailWord_5233562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233562).length < 2 ^ (prefixWord ++ tailWord_5233562).sum := by decide
  have hdescent : baseEnd_5233562 < baseStart_5233562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233568 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 1, 1, 4]
def baseStart_5233568 : Nat := 118140960795 + 5233568 * 2 ^ 59
def prefixEnd_5233568 : Nat := 4983230072969 + 3 ^ 40 * 5233568 * 2
def baseEnd_5233568 : Nat := 2687335921989884874831265

theorem tailTrace_5233568 : CollatzResearch.WordTrace tailWord_5233568 prefixEnd_5233568 2687335921989884874831265 := by
  unfold tailWord_5233568
  simp only [CollatzResearch.WordTrace]
  refine ⟨95441953351842216549342679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127255937802456288732456905 95441953351842216549342679)
  ·
    refine ⟨143162930027763324824014019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95441953351842216549342679 143162930027763324824014019)
    ·
      refine ⟨214744395041644987236021029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143162930027763324824014019 214744395041644987236021029)
      ·
        refine ⟨40264574070308435106753943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214744395041644987236021029 40264574070308435106753943)
        ·
          refine ⟨60396861105462652660130915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40264574070308435106753943 60396861105462652660130915)
          ·
            refine ⟨90595291658193978990196373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60396861105462652660130915 90595291658193978990196373)
            ·
              refine ⟨4246654296477842765165455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90595291658193978990196373 4246654296477842765165455)
              ·
                refine ⟨6369981444716764147748183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4246654296477842765165455 6369981444716764147748183)
                ·
                  refine ⟨9554972167075146221622275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6369981444716764147748183 9554972167075146221622275)
                  ·
                    refine ⟨14332458250612719332433413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9554972167075146221622275 14332458250612719332433413)
                    ·
                      refine ⟨2687335921989884874831265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14332458250612719332433413 2687335921989884874831265)
                      ·
                        rfl

theorem cell23_5233568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_5233568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233568 prefixEnd_5233568 := by exact prefixLift 5233568
  have htrace : WordTrace (prefixWord ++ tailWord_5233568) baseStart_5233568 baseEnd_5233568 := by
    simpa [prefixWord, tailWord_5233568, baseEnd_5233568] using wordTrace_append hprefix tailTrace_5233568
  have hstable : (prefixWord ++ tailWord_5233568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233568).length < 2 ^ (prefixWord ++ tailWord_5233568).sum := by decide
  have hdescent : baseEnd_5233568 < baseStart_5233568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233584 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 3]
def baseStart_5233584 : Nat := 118140960795 + 5233584 * 2 ^ 59
def prefixEnd_5233584 : Nat := 4983230072969 + 3 ^ 40 * 5233584 * 2
def baseEnd_5233584 : Nat := 2687344137680356812231191

theorem tailTrace_5233584 : CollatzResearch.WordTrace tailWord_5233584 prefixEnd_5233584 2687344137680356812231191 := by
  unfold tailWord_5233584
  simp only [CollatzResearch.WordTrace]
  refine ⟨95442245135813233915633903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127256326847750978554178537 95442245135813233915633903)
  ·
    refine ⟨143163367703719850873450855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95442245135813233915633903 143163367703719850873450855)
    ·
      refine ⟨214745051555579776310176283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143163367703719850873450855 214745051555579776310176283)
      ·
        refine ⟨322117577333369664465264425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214745051555579776310176283 322117577333369664465264425)
        ·
          refine ⟨241588183000027248348948319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322117577333369664465264425 241588183000027248348948319)
          ·
            refine ⟨362382274500040872523422479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241588183000027248348948319 362382274500040872523422479)
            ·
              refine ⟨543573411750061308785133719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362382274500040872523422479 543573411750061308785133719)
              ·
                refine ⟨815360117625091963177700579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543573411750061308785133719 815360117625091963177700579)
                ·
                  refine ⟨1223040176437637944766550869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 815360117625091963177700579 1223040176437637944766550869)
                  ·
                    refine ⟨7166251033814284832616509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1223040176437637944766550869 7166251033814284832616509)
                    ·
                      refine ⟨2687344137680356812231191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7166251033814284832616509 2687344137680356812231191)
                      ·
                        rfl

theorem cell23_5233584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_5233584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233584 prefixEnd_5233584 := by exact prefixLift 5233584
  have htrace : WordTrace (prefixWord ++ tailWord_5233584) baseStart_5233584 baseEnd_5233584 := by
    simpa [prefixWord, tailWord_5233584, baseEnd_5233584] using wordTrace_append hprefix tailTrace_5233584
  have hstable : (prefixWord ++ tailWord_5233584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233584).length < 2 ^ (prefixWord ++ tailWord_5233584).sum := by decide
  have hdescent : baseEnd_5233584 < baseStart_5233584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233588 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5233588 : Nat := 118140960795 + 5233588 * 2 ^ 59
def prefixEnd_5233588 : Nat := 4983230072969 + 3 ^ 40 * 5233588 * 2
def baseEnd_5233588 : Nat := 2687346191602974796581173

theorem tailTrace_5233588 : CollatzResearch.WordTrace tailWord_5233588 prefixEnd_5233588 2687346191602974796581173 := by
  unfold tailWord_5233588
  simp only [CollatzResearch.WordTrace]
  refine ⟨95442318081805988257206709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127256424109074651009608945 95442318081805988257206709)
  ·
    refine ⟨8947717320169311399113129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95442318081805988257206709 8947717320169311399113129)
    ·
      refine ⟨6710787990126983549334847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8947717320169311399113129 6710787990126983549334847)
      ·
        refine ⟨10066181985190475324002271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6710787990126983549334847 10066181985190475324002271)
        ·
          refine ⟨15099272977785712986003407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10066181985190475324002271 15099272977785712986003407)
          ·
            refine ⟨22648909466678569479005111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15099272977785712986003407 22648909466678569479005111)
            ·
              refine ⟨33973364200017854218507667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22648909466678569479005111 33973364200017854218507667)
              ·
                refine ⟨50960046300026781327761501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33973364200017854218507667 50960046300026781327761501)
                ·
                  refine ⟨19110017362510042997910563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50960046300026781327761501 19110017362510042997910563)
                  ·
                    refine ⟨28665026043765064496865845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19110017362510042997910563 28665026043765064496865845)
                    ·
                      refine ⟨2687346191602974796581173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28665026043765064496865845 2687346191602974796581173)
                      ·
                        rfl

theorem cell23_5233588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5233588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233588 prefixEnd_5233588 := by exact prefixLift 5233588
  have htrace : WordTrace (prefixWord ++ tailWord_5233588) baseStart_5233588 baseEnd_5233588 := by
    simpa [prefixWord, tailWord_5233588, baseEnd_5233588] using wordTrace_append hprefix tailTrace_5233588
  have hstable : (prefixWord ++ tailWord_5233588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233588).length < 2 ^ (prefixWord ++ tailWord_5233588).sum := by decide
  have hdescent : baseEnd_5233588 < baseStart_5233588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233608 : List Nat := [2, 1, 3, 1, 5, 2, 2, 7]
def baseStart_5233608 : Nat := 118140960795 + 5233608 * 2 ^ 59
def prefixEnd_5233608 : Nat := 4983230072969 + 3 ^ 40 * 5233608 * 2
def baseEnd_5233608 : Nat := 99531720785780174753003

theorem tailTrace_5233608 : CollatzResearch.WordTrace tailWord_5233608 prefixEnd_5233608 99531720785780174753003 := by
  unfold tailWord_5233608
  simp only [CollatzResearch.WordTrace]
  refine ⟨95442682811769759965070739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127256910415693013286760985 95442682811769759965070739)
  ·
    refine ⟨143164024217654639947606109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95442682811769759965070739 143164024217654639947606109)
    ·
      refine ⟨53686509081620489980352291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143164024217654639947606109 53686509081620489980352291)
      ·
        refine ⟨80529763622430734970528437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53686509081620489980352291 80529763622430734970528437)
        ·
          refine ⟨7549665339602881403487041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80529763622430734970528437 7549665339602881403487041)
          ·
            refine ⟨5662249004702161052615281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7549665339602881403487041 5662249004702161052615281)
            ·
              refine ⟨4246686753526620789461461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5662249004702161052615281 4246686753526620789461461)
              ·
                refine ⟨99531720785780174753003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4246686753526620789461461 99531720785780174753003)
                ·
                  rfl

theorem cell23_5233608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 7].length) (baseStart_5233608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233608 prefixEnd_5233608 := by exact prefixLift 5233608
  have htrace : WordTrace (prefixWord ++ tailWord_5233608) baseStart_5233608 baseEnd_5233608 := by
    simpa [prefixWord, tailWord_5233608, baseEnd_5233608] using wordTrace_append hprefix tailTrace_5233608
  have hstable : (prefixWord ++ tailWord_5233608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233608).length < 2 ^ (prefixWord ++ tailWord_5233608).sum := by decide
  have hdescent : baseEnd_5233608 < baseStart_5233608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233613 : List Nat := [1, 6, 3, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5233613 : Nat := 118140960795 + 5233613 * 2 ^ 59
def prefixEnd_5233613 : Nat := 4983230072969 + 3 ^ 40 * 5233613 * 2
def baseEnd_5233613 : Nat := 2687359028619337198768559

theorem tailTrace_5233613 : CollatzResearch.WordTrace tailWord_5233613 prefixEnd_5233613 2687359028619337198768559 := by
  unfold tailWord_5233613
  simp only [CollatzResearch.WordTrace]
  refine ⟨190885547988521405784073493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127257031992347603856048995 190885547988521405784073493)
  ·
    refine ⟨8947760061961940896128445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 190885547988521405784073493 8947760061961940896128445)
    ·
      refine ⟨3355410023235727836048167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8947760061961940896128445 3355410023235727836048167)
      ·
        refine ⟨5033115034853591754072251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3355410023235727836048167 5033115034853591754072251)
        ·
          refine ⟨7549672552280387631108377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033115034853591754072251 7549672552280387631108377)
          ·
            refine ⟨5662254414210290723331283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7549672552280387631108377 5662254414210290723331283)
            ·
              refine ⟨8493381621315436084996925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662254414210290723331283 8493381621315436084996925)
              ·
                refine ⟨3185018107993288531873847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8493381621315436084996925 3185018107993288531873847)
                ·
                  refine ⟨4777527161989932797810771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185018107993288531873847 4777527161989932797810771)
                  ·
                    refine ⟨7166290742984899196716157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4777527161989932797810771 7166290742984899196716157)
                    ·
                      refine ⟨2687359028619337198768559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7166290742984899196716157 2687359028619337198768559)
                      ·
                        rfl

theorem cell23_5233613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5233613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233613 prefixEnd_5233613 := by exact prefixLift 5233613
  have htrace : WordTrace (prefixWord ++ tailWord_5233613) baseStart_5233613 baseEnd_5233613 := by
    simpa [prefixWord, tailWord_5233613, baseEnd_5233613] using wordTrace_append hprefix tailTrace_5233613
  have hstable : (prefixWord ++ tailWord_5233613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233613).length < 2 ^ (prefixWord ++ tailWord_5233613).sum := by decide
  have hdescent : baseEnd_5233613 < baseStart_5233613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233662 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_5233662 : Nat := 118140960795 + 5233662 * 2 ^ 59
def prefixEnd_5233662 : Nat := 4983230072969 + 3 ^ 40 * 5233662 * 2
def baseEnd_5233662 : Nat := 2687384189171407507055833

theorem tailTrace_5233662 : CollatzResearch.WordTrace tailWord_5233662 prefixEnd_5233662 2687384189171407507055833 := by
  unfold tailWord_5233662
  simp only [CollatzResearch.WordTrace]
  refine ⟨23860916895667985894075905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127258223443562591435071493 23860916895667985894075905)
  ·
    refine ⟨17895687671750989420556929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23860916895667985894075905 17895687671750989420556929)
    ·
      refine ⟨13421765753813242065417697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17895687671750989420556929 13421765753813242065417697)
      ·
        refine ⟨10066324315359931549063273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13421765753813242065417697 10066324315359931549063273)
        ·
          refine ⟨7549743236519948661797455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10066324315359931549063273 7549743236519948661797455)
          ·
            refine ⟨11324614854779922992696183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7549743236519948661797455 11324614854779922992696183)
            ·
              refine ⟨16986922282169884489044275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11324614854779922992696183 16986922282169884489044275)
              ·
                refine ⟨25480383423254826733566413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16986922282169884489044275 25480383423254826733566413)
                ·
                  refine ⟨9555143783720560025087405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25480383423254826733566413 9555143783720560025087405)
                  ·
                    refine ⟨3583178918895210009407777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9555143783720560025087405 3583178918895210009407777)
                    ·
                      refine ⟨2687384189171407507055833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583178918895210009407777 2687384189171407507055833)
                      ·
                        rfl

theorem cell23_5233662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_5233662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233662 prefixEnd_5233662 := by exact prefixLift 5233662
  have htrace : WordTrace (prefixWord ++ tailWord_5233662) baseStart_5233662 baseEnd_5233662 := by
    simpa [prefixWord, tailWord_5233662, baseEnd_5233662] using wordTrace_append hprefix tailTrace_5233662
  have hstable : (prefixWord ++ tailWord_5233662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233662).length < 2 ^ (prefixWord ++ tailWord_5233662).sum := by decide
  have hdescent : baseEnd_5233662 < baseStart_5233662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233731 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 4]
def baseStart_5233731 : Nat := 118140960795 + 5233731 * 2 ^ 59
def prefixEnd_5233731 : Nat := 4983230072969 + 3 ^ 40 * 5233731 * 2
def baseEnd_5233731 : Nat := 2687419619336567737093015

theorem tailTrace_5233731 : CollatzResearch.WordTrace tailWord_5233731 prefixEnd_5233731 2687419619336567737093015 := by
  unfold tailWord_5233731
  simp only [CollatzResearch.WordTrace]
  refine ⟨190889851802093911936869047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127259901201395941291246031 190889851802093911936869047)
  ·
    refine ⟨286334777703140867905303571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190889851802093911936869047 286334777703140867905303571)
    ·
      refine ⟨429502166554711301857955357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286334777703140867905303571 429502166554711301857955357)
      ·
        refine ⟨161063312458016738196733259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 429502166554711301857955357 161063312458016738196733259)
        ·
          refine ⟨241594968687025107295099889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161063312458016738196733259 241594968687025107295099889)
          ·
            refine ⟨181196226515268830471324917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241594968687025107295099889 181196226515268830471324917)
            ·
              refine ⟨16987146235806452856686711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181196226515268830471324917 16987146235806452856686711)
              ·
                refine ⟨25480719353709679285030067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16987146235806452856686711 25480719353709679285030067)
                ·
                  refine ⟨38221079030564518927545101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25480719353709679285030067 38221079030564518927545101)
                  ·
                    refine ⟨14332904636461694597829413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38221079030564518927545101 14332904636461694597829413)
                    ·
                      refine ⟨2687419619336567737093015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14332904636461694597829413 2687419619336567737093015)
                      ·
                        rfl

theorem cell23_5233731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_5233731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233731 prefixEnd_5233731 := by exact prefixLift 5233731
  have htrace : WordTrace (prefixWord ++ tailWord_5233731) baseStart_5233731 baseEnd_5233731 := by
    simpa [prefixWord, tailWord_5233731, baseEnd_5233731] using wordTrace_append hprefix tailTrace_5233731
  have hstable : (prefixWord ++ tailWord_5233731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233731).length < 2 ^ (prefixWord ++ tailWord_5233731).sum := by decide
  have hdescent : baseEnd_5233731 < baseStart_5233731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233748 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_5233748 : Nat := 118140960795 + 5233748 * 2 ^ 59
def prefixEnd_5233748 : Nat := 4983230072969 + 3 ^ 40 * 5233748 * 2
def baseEnd_5233748 : Nat := 2687428348507694170580437

theorem tailTrace_5233748 : CollatzResearch.WordTrace tailWord_5233748 prefixEnd_5233748 2687428348507694170580437 := by
  unfold tailWord_5233748
  simp only [CollatzResearch.WordTrace]
  refine ⟨95445235921516161920118949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127260314562021549226825265 95445235921516161920118949)
  ·
    refine ⟨17895981735284280360022303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95445235921516161920118949 17895981735284280360022303)
    ·
      refine ⟨26843972602926420540033455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17895981735284280360022303 26843972602926420540033455)
      ·
        refine ⟨40265958904389630810050183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26843972602926420540033455 40265958904389630810050183)
        ·
          refine ⟨60398938356584446215075275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40265958904389630810050183 60398938356584446215075275)
          ·
            refine ⟨90598407534876669322612913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60398938356584446215075275 90598407534876669322612913)
            ·
              refine ⟨67948805651157501991959685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90598407534876669322612913 67948805651157501991959685)
              ·
                refine ⟨12740401059592031623492441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67948805651157501991959685 12740401059592031623492441)
                ·
                  refine ⟨9555300794694023717619331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12740401059592031623492441 9555300794694023717619331)
                  ·
                    refine ⟨14332951192041035576428997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9555300794694023717619331 14332951192041035576428997)
                    ·
                      refine ⟨2687428348507694170580437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14332951192041035576428997 2687428348507694170580437)
                      ·
                        rfl

theorem cell23_5233748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_5233748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233748 prefixEnd_5233748 := by exact prefixLift 5233748
  have htrace : WordTrace (prefixWord ++ tailWord_5233748) baseStart_5233748 baseEnd_5233748 := by
    simpa [prefixWord, tailWord_5233748, baseEnd_5233748] using wordTrace_append hprefix tailTrace_5233748
  have hstable : (prefixWord ++ tailWord_5233748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233748).length < 2 ^ (prefixWord ++ tailWord_5233748).sum := by decide
  have hdescent : baseEnd_5233748 < baseStart_5233748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233808 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 3, 5, 2]
def baseStart_5233808 : Nat := 118140960795 + 5233808 * 2 ^ 59
def prefixEnd_5233808 : Nat := 4983230072969 + 3 ^ 40 * 5233808 * 2
def baseEnd_5233808 : Nat := 2687459157346963935830161

theorem tailTrace_5233808 : CollatzResearch.WordTrace tailWord_5233808 prefixEnd_5233808 2687459157346963935830161 := by
  unfold tailWord_5233808
  simp only [CollatzResearch.WordTrace]
  refine ⟨95446330111407477043711039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127261773481876636058281385 95446330111407477043711039)
  ·
    refine ⟨143169495167111215565566559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95446330111407477043711039 143169495167111215565566559)
    ·
      refine ⟨214754242750666823348349839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143169495167111215565566559 214754242750666823348349839)
      ·
        refine ⟨322131364126000235022524759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214754242750666823348349839 322131364126000235022524759)
        ·
          refine ⟨483197046189000352533787139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322131364126000235022524759 483197046189000352533787139)
          ·
            refine ⟨724795569283500528800680709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483197046189000352533787139 724795569283500528800680709)
            ·
              refine ⟨135899169240656349150127633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 724795569283500528800680709 135899169240656349150127633)
              ·
                refine ⟨101924376930492261862595725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135899169240656349150127633 101924376930492261862595725)
                ·
                  refine ⟨38221641348934598198473397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101924376930492261862595725 38221641348934598198473397)
                  ·
                    refine ⟨3583278876462618581106881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38221641348934598198473397 3583278876462618581106881)
                    ·
                      refine ⟨2687459157346963935830161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583278876462618581106881 2687459157346963935830161)
                      ·
                        rfl

theorem cell23_5233808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 3, 5, 2].length) (baseStart_5233808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233808 prefixEnd_5233808 := by exact prefixLift 5233808
  have htrace : WordTrace (prefixWord ++ tailWord_5233808) baseStart_5233808 baseEnd_5233808 := by
    simpa [prefixWord, tailWord_5233808, baseEnd_5233808] using wordTrace_append hprefix tailTrace_5233808
  have hstable : (prefixWord ++ tailWord_5233808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233808).length < 2 ^ (prefixWord ++ tailWord_5233808).sum := by decide
  have hdescent : baseEnd_5233808 < baseStart_5233808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233822 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_5233822 : Nat := 118140960795 + 5233822 * 2 ^ 59
def prefixEnd_5233822 : Nat := 4983230072969 + 3 ^ 40 * 5233822 * 2
def baseEnd_5233822 : Nat := 298607371786236320117233

theorem tailTrace_5233822 : CollatzResearch.WordTrace tailWord_5233822 prefixEnd_5233822 298607371786236320117233 := by
  unfold tailWord_5233822
  simp only [CollatzResearch.WordTrace]
  refine ⟨23861646355595529309803965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127262113896509489652287813 23861646355595529309803965)
  ·
    refine ⟨8948117383348323491176487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23861646355595529309803965 8948117383348323491176487)
    ·
      refine ⟨13422176075022485236764731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8948117383348323491176487 13422176075022485236764731)
      ·
        refine ⟨20133264112533727855147097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13422176075022485236764731 20133264112533727855147097)
        ·
          refine ⟨15099948084400295891360323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20133264112533727855147097 15099948084400295891360323)
          ·
            refine ⟨22649922126600443837040485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15099948084400295891360323 22649922126600443837040485)
            ·
              refine ⟨4246860398737583219445091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22649922126600443837040485 4246860398737583219445091)
              ·
                refine ⟨6370290598106374829167637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4246860398737583219445091 6370290598106374829167637)
                ·
                  refine ⟨298607371786236320117233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6370290598106374829167637 298607371786236320117233)
                  ·
                    rfl

theorem cell23_5233822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_5233822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233822 prefixEnd_5233822 := by exact prefixLift 5233822
  have htrace : WordTrace (prefixWord ++ tailWord_5233822) baseStart_5233822 baseEnd_5233822 := by
    simpa [prefixWord, tailWord_5233822, baseEnd_5233822] using wordTrace_append hprefix tailTrace_5233822
  have hstable : (prefixWord ++ tailWord_5233822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233822).length < 2 ^ (prefixWord ++ tailWord_5233822).sum := by decide
  have hdescent : baseEnd_5233822 < baseStart_5233822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233825 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 4, 3, 2]
def baseStart_5233825 : Nat := 118140960795 + 5233825 * 2 ^ 59
def prefixEnd_5233825 : Nat := 4983230072969 + 3 ^ 40 * 5233825 * 2
def baseEnd_5233825 : Nat := 2687467886518090369317583

theorem tailTrace_5233825 : CollatzResearch.WordTrace tailWord_5233825 prefixEnd_5233825 2687467886518090369317583 := by
  unfold tailWord_5233825
  simp only [CollatzResearch.WordTrace]
  refine ⟨190893280263753365990790929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127262186842502243993860619 190893280263753365990790929)
  ·
    refine ⟨143169960197815024493093197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190893280263753365990790929 143169960197815024493093197)
    ·
      refine ⟨53688735074180634184909949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143169960197815024493093197 53688735074180634184909949)
      ·
        refine ⟨20133275652817737819341231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53688735074180634184909949 20133275652817737819341231)
        ·
          refine ⟨30199913479226606729011847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20133275652817737819341231 30199913479226606729011847)
          ·
            refine ⟨45299870218839910093517771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30199913479226606729011847 45299870218839910093517771)
            ·
              refine ⟨67949805328259865140276657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45299870218839910093517771 67949805328259865140276657)
              ·
                refine ⟨50962353996194898855207493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67949805328259865140276657 50962353996194898855207493)
                ·
                  refine ⟨9555441374286543535351405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50962353996194898855207493 9555441374286543535351405)
                  ·
                    refine ⟨3583290515357453825756777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9555441374286543535351405 3583290515357453825756777)
                    ·
                      refine ⟨2687467886518090369317583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583290515357453825756777 2687467886518090369317583)
                      ·
                        rfl

theorem cell23_5233825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_5233825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233825 prefixEnd_5233825 := by exact prefixLift 5233825
  have htrace : WordTrace (prefixWord ++ tailWord_5233825) baseStart_5233825 baseEnd_5233825 := by
    simpa [prefixWord, tailWord_5233825, baseEnd_5233825] using wordTrace_append hprefix tailTrace_5233825
  have hstable : (prefixWord ++ tailWord_5233825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233825).length < 2 ^ (prefixWord ++ tailWord_5233825).sum := by decide
  have hdescent : baseEnd_5233825 < baseStart_5233825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233842 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_5233842 : Nat := 118140960795 + 5233842 * 2 ^ 59
def prefixEnd_5233842 : Nat := 4983230072969 + 3 ^ 40 * 5233842 * 2
def baseEnd_5233842 : Nat := 2687476615689216802805005

theorem tailTrace_5233842 : CollatzResearch.WordTrace tailWord_5233842 prefixEnd_5233842 2687476615689216802805005 := by
  unfold tailWord_5233842
  simp only [CollatzResearch.WordTrace]
  refine ⟨47723475076172944473539945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127262600203127851929439853 47723475076172944473539945)
  ·
    refine ⟨35792606307129708355154959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47723475076172944473539945 35792606307129708355154959)
    ·
      refine ⟨53688909460694562532732439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35792606307129708355154959 53688909460694562532732439)
      ·
        refine ⟨80533364191041843799098659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53688909460694562532732439 80533364191041843799098659)
        ·
          refine ⟨120800046286562765698647989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80533364191041843799098659 120800046286562765698647989)
          ·
            refine ⟨11325004339365259284248249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120800046286562765698647989 11325004339365259284248249)
            ·
              refine ⟨8493753254523944463186187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11325004339365259284248249 8493753254523944463186187)
              ·
                refine ⟨12740629881785916694779281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8493753254523944463186187 12740629881785916694779281)
                ·
                  refine ⟨9555472411339437521084461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12740629881785916694779281 9555472411339437521084461)
                  ·
                    refine ⟨3583302154252289070406673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9555472411339437521084461 3583302154252289070406673)
                    ·
                      refine ⟨2687476615689216802805005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583302154252289070406673 2687476615689216802805005)
                      ·
                        rfl

theorem cell23_5233842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_5233842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233842 prefixEnd_5233842 := by exact prefixLift 5233842
  have htrace : WordTrace (prefixWord ++ tailWord_5233842) baseStart_5233842 baseEnd_5233842 := by
    simpa [prefixWord, tailWord_5233842, baseEnd_5233842] using wordTrace_append hprefix tailTrace_5233842
  have hstable : (prefixWord ++ tailWord_5233842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233842).length < 2 ^ (prefixWord ++ tailWord_5233842).sum := by decide
  have hdescent : baseEnd_5233842 < baseStart_5233842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233848 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 4, 4]
def baseStart_5233848 : Nat := 118140960795 + 5233848 * 2 ^ 59
def prefixEnd_5233848 : Nat := 4983230072969 + 3 ^ 40 * 5233848 * 2
def baseEnd_5233848 : Nat := 895826565524381259776659

theorem tailTrace_5233848 : CollatzResearch.WordTrace tailWord_5233848 prefixEnd_5233848 895826565524381259776659 := by
  unfold tailWord_5233848
  simp only [CollatzResearch.WordTrace]
  refine ⟨95447059571335020459439099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127262746095113360612585465 95447059571335020459439099)
  ·
    refine ⟨143170589357002530689158649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95447059571335020459439099 143170589357002530689158649)
    ·
      refine ⟨107377942017751898016868987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143170589357002530689158649 107377942017751898016868987)
      ·
        refine ⟨161066913026627847025303481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107377942017751898016868987 161066913026627847025303481)
        ·
          refine ⟨120800184769970885268977611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161066913026627847025303481 120800184769970885268977611)
          ·
            refine ⟨181200277154956327903466417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120800184769970885268977611 181200277154956327903466417)
            ·
              refine ⟨135900207866217245927599813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181200277154956327903466417 135900207866217245927599813)
              ·
                refine ⟨25481288974915733611424965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135900207866217245927599813 25481288974915733611424965)
                ·
                  refine ⟨4777741682796700052142181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25481288974915733611424965 4777741682796700052142181)
                  ·
                    refine ⟨895826565524381259776659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4777741682796700052142181 895826565524381259776659)
                    ·
                      rfl

theorem cell23_5233848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_5233848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233848 prefixEnd_5233848 := by exact prefixLift 5233848
  have htrace : WordTrace (prefixWord ++ tailWord_5233848) baseStart_5233848 baseEnd_5233848 := by
    simpa [prefixWord, tailWord_5233848, baseEnd_5233848] using wordTrace_append hprefix tailTrace_5233848
  have hstable : (prefixWord ++ tailWord_5233848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233848).length < 2 ^ (prefixWord ++ tailWord_5233848).sum := by decide
  have hdescent : baseEnd_5233848 < baseStart_5233848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233851 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 6]
def baseStart_5233851 : Nat := 118140960795 + 5233851 * 2 ^ 59
def prefixEnd_5233851 : Nat := 4983230072969 + 3 ^ 40 * 5233851 * 2
def baseEnd_5233851 : Nat := 2687481237015107267592463

theorem tailTrace_5233851 : CollatzResearch.WordTrace tailWord_5233851 prefixEnd_5233851 2687481237015107267592463 := by
  unfold tailWord_5233851
  simp only [CollatzResearch.WordTrace]
  refine ⟨190894228561659172431237407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127262819041106114954158271 190894228561659172431237407)
  ·
    refine ⟨286341342842488758646856111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190894228561659172431237407 286341342842488758646856111)
    ·
      refine ⟨429512014263733137970284167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286341342842488758646856111 429512014263733137970284167)
      ·
        refine ⟨644268021395599706955426251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429512014263733137970284167 644268021395599706955426251)
        ·
          refine ⟨966402032093399560433139377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644268021395599706955426251 966402032093399560433139377)
          ·
            refine ⟨724801524070049670324854533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966402032093399560433139377 724801524070049670324854533)
            ·
              refine ⟨135900285763134313185910225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 724801524070049670324854533 135900285763134313185910225)
              ·
                refine ⟨101925214322350734889432669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135900285763134313185910225 101925214322350734889432669)
                ·
                  refine ⟨38221955370881525583537251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101925214322350734889432669 38221955370881525583537251)
                  ·
                    refine ⟨57332933056322288375305877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38221955370881525583537251 57332933056322288375305877)
                    ·
                      refine ⟨2687481237015107267592463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57332933056322288375305877 2687481237015107267592463)
                      ·
                        rfl

theorem cell23_5233851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_5233851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233851 prefixEnd_5233851 := by exact prefixLift 5233851
  have htrace : WordTrace (prefixWord ++ tailWord_5233851) baseStart_5233851 baseEnd_5233851 := by
    simpa [prefixWord, tailWord_5233851, baseEnd_5233851] using wordTrace_append hprefix tailTrace_5233851
  have hstable : (prefixWord ++ tailWord_5233851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233851).length < 2 ^ (prefixWord ++ tailWord_5233851).sum := by decide
  have hdescent : baseEnd_5233851 < baseStart_5233851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233852 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_5233852 : Nat := 118140960795 + 5233852 * 2 ^ 59
def prefixEnd_5233852 : Nat := 4983230072969 + 3 ^ 40 * 5233852 * 2
def baseEnd_5233852 : Nat := 895827250165253921226653

theorem tailTrace_5233852 : CollatzResearch.WordTrace tailWord_5233852 prefixEnd_5233852 895827250165253921226653 := by
  unfold tailWord_5233852
  simp only [CollatzResearch.WordTrace]
  refine ⟨95447132517327774801011905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127262843356437033068015873 95447132517327774801011905)
  ·
    refine ⟨71585349387995831100758929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95447132517327774801011905 71585349387995831100758929)
    ·
      refine ⟨53689012040996873325569197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71585349387995831100758929 53689012040996873325569197)
      ·
        refine ⟨20133379515373827497088449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53689012040996873325569197 20133379515373827497088449)
        ·
          refine ⟨15100034636530370622816337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20133379515373827497088449 15100034636530370622816337)
          ·
            refine ⟨11325025977397777967112253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15100034636530370622816337 11325025977397777967112253)
            ·
              refine ⟨4246884741524166737667095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11325025977397777967112253 4246884741524166737667095)
              ·
                refine ⟨6370327112286250106500643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4246884741524166737667095 6370327112286250106500643)
                ·
                  refine ⟨9555490668429375159750965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6370327112286250106500643 9555490668429375159750965)
                  ·
                    refine ⟨895827250165253921226653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9555490668429375159750965 895827250165253921226653)
                    ·
                      rfl

theorem cell23_5233852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_5233852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233852 prefixEnd_5233852 := by exact prefixLift 5233852
  have htrace : WordTrace (prefixWord ++ tailWord_5233852) baseStart_5233852 baseEnd_5233852 := by
    simpa [prefixWord, tailWord_5233852, baseEnd_5233852] using wordTrace_append hprefix tailTrace_5233852
  have hstable : (prefixWord ++ tailWord_5233852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233852).length < 2 ^ (prefixWord ++ tailWord_5233852).sum := by decide
  have hdescent : baseEnd_5233852 < baseStart_5233852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233866 : List Nat := [3, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3]
def baseStart_5233866 : Nat := 118140960795 + 5233866 * 2 ^ 59
def prefixEnd_5233866 : Nat := 4983230072969 + 3 ^ 40 * 5233866 * 2
def baseEnd_5233866 : Nat := 2687488939224924708904895

theorem tailTrace_5233866 : CollatzResearch.WordTrace tailWord_5233866 prefixEnd_5233866 2687488939224924708904895 := by
  unfold tailWord_5233866
  simp only [CollatzResearch.WordTrace]
  refine ⟨47723693914151207498258363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127263183771069886662022301 47723693914151207498258363)
  ·
    refine ⟨71585540871226811247387545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47723693914151207498258363 71585540871226811247387545)
    ·
      refine ⟨53689155653420108435540659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71585540871226811247387545 53689155653420108435540659)
      ·
        refine ⟨80533733480130162653310989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53689155653420108435540659 80533733480130162653310989)
        ·
          refine ⟨30200150055048810994991621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80533733480130162653310989 30200150055048810994991621)
          ·
            refine ⟨5662528135321652061560929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30200150055048810994991621 5662528135321652061560929)
            ·
              refine ⟨4246896101491239046170697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5662528135321652061560929 4246896101491239046170697)
              ·
                refine ⟨3185172076118429284628023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4246896101491239046170697 3185172076118429284628023)
                ·
                  refine ⟨4777758114177643926942035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185172076118429284628023 4777758114177643926942035)
                  ·
                    refine ⟨7166637171266465890413053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4777758114177643926942035 7166637171266465890413053)
                    ·
                      refine ⟨2687488939224924708904895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7166637171266465890413053 2687488939224924708904895)
                      ·
                        rfl

theorem cell23_5233866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_5233866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233866 prefixEnd_5233866 := by exact prefixLift 5233866
  have htrace : WordTrace (prefixWord ++ tailWord_5233866) baseStart_5233866 baseEnd_5233866 := by
    simpa [prefixWord, tailWord_5233866, baseEnd_5233866] using wordTrace_append hprefix tailTrace_5233866
  have hstable : (prefixWord ++ tailWord_5233866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233866).length < 2 ^ (prefixWord ++ tailWord_5233866).sum := by decide
  have hdescent : baseEnd_5233866 < baseStart_5233866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233871 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_5233871 : Nat := 118140960795 + 5233871 * 2 ^ 59
def prefixEnd_5233871 : Nat := 4983230072969 + 3 ^ 40 * 5233871 * 2
def baseEnd_5233871 : Nat := 2687491506628197189342371

theorem tailTrace_5233871 : CollatzResearch.WordTrace tailWord_5233871 prefixEnd_5233871 2687491506628197189342371 := by
  unfold tailWord_5233871
  simp only [CollatzResearch.WordTrace]
  refine ⟨190894958021586715846965467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127263305347724477231310311 190894958021586715846965467)
  ·
    refine ⟨286342437032380073770448201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190894958021586715846965467 286342437032380073770448201)
    ·
      refine ⟨214756827774285055327836151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286342437032380073770448201 214756827774285055327836151)
      ·
        refine ⟨322135241661427582991754227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214756827774285055327836151 322135241661427582991754227)
        ·
          refine ⟨483202862492141374487631341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322135241661427582991754227 483202862492141374487631341)
          ·
            refine ⟨181201073434553015432861753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 483202862492141374487631341 181201073434553015432861753)
            ·
              refine ⟨135900805075914761574646315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181201073434553015432861753 135900805075914761574646315)
              ·
                refine ⟨203851207613872142361969473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135900805075914761574646315 203851207613872142361969473)
                ·
                  refine ⟨152888405710404106771477105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203851207613872142361969473 152888405710404106771477105)
                  ·
                    refine ⟨114666304282803080078607829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152888405710404106771477105 114666304282803080078607829)
                    ·
                      refine ⟨2687491506628197189342371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114666304282803080078607829 2687491506628197189342371)
                      ·
                        rfl

theorem cell23_5233871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_5233871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233871 prefixEnd_5233871 := by exact prefixLift 5233871
  have htrace : WordTrace (prefixWord ++ tailWord_5233871) baseStart_5233871 baseEnd_5233871 := by
    simpa [prefixWord, tailWord_5233871, baseEnd_5233871] using wordTrace_append hprefix tailTrace_5233871
  have hstable : (prefixWord ++ tailWord_5233871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233871).length < 2 ^ (prefixWord ++ tailWord_5233871).sum := by decide
  have hdescent : baseEnd_5233871 < baseStart_5233871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233905 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 3]
def baseStart_5233905 : Nat := 118140960795 + 5233905 * 2 ^ 59
def prefixEnd_5233905 : Nat := 4983230072969 + 3 ^ 40 * 5233905 * 2
def baseEnd_5233905 : Nat := 2687508964970450056317215

theorem tailTrace_5233905 : CollatzResearch.WordTrace tailWord_5233905 prefixEnd_5233905 2687508964970450056317215 := by
  unfold tailWord_5233905
  simp only [CollatzResearch.WordTrace]
  refine ⟨190896198103463539653703169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127264132068975693102468779 190896198103463539653703169)
  ·
    refine ⟨143172148577597654740277377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190896198103463539653703169 143172148577597654740277377)
    ·
      refine ⟨107379111433198241055208033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143172148577597654740277377 107379111433198241055208033)
      ·
        refine ⟨80534333574898680791406025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107379111433198241055208033 80534333574898680791406025)
        ·
          refine ⟨60400750181174010593554519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80534333574898680791406025 60400750181174010593554519)
          ·
            refine ⟨90601125271761015890331779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60400750181174010593554519 90601125271761015890331779)
            ·
              refine ⟨135901687907641523835497669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90601125271761015890331779 135901687907641523835497669)
              ·
                refine ⟨25481566482682785719155813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135901687907641523835497669 25481566482682785719155813)
                ·
                  refine ⟨4777793715503022322341715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25481566482682785719155813 4777793715503022322341715)
                  ·
                    refine ⟨7166690573254533483512573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4777793715503022322341715 7166690573254533483512573)
                    ·
                      refine ⟨2687508964970450056317215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7166690573254533483512573 2687508964970450056317215)
                      ·
                        rfl

theorem cell23_5233905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_5233905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233905 prefixEnd_5233905 := by exact prefixLift 5233905
  have htrace : WordTrace (prefixWord ++ tailWord_5233905) baseStart_5233905 baseEnd_5233905 := by
    simpa [prefixWord, tailWord_5233905, baseEnd_5233905] using wordTrace_append hprefix tailTrace_5233905
  have hstable : (prefixWord ++ tailWord_5233905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233905).length < 2 ^ (prefixWord ++ tailWord_5233905).sum := by decide
  have hdescent : baseEnd_5233905 < baseStart_5233905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233906 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_5233906 : Nat := 118140960795 + 5233906 * 2 ^ 59
def prefixEnd_5233906 : Nat := 4983230072969 + 3 ^ 40 * 5233906 * 2
def baseEnd_5233906 : Nat := 2687509478451104552404711

theorem tailTrace_5233906 : CollatzResearch.WordTrace tailWord_5233906 prefixEnd_5233906 2687509478451104552404711 := by
  unfold tailWord_5233906
  simp only [CollatzResearch.WordTrace]
  refine ⟨47724058644114979206122393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127264156384306611216326381 47724058644114979206122393)
  ·
    refine ⟨35793043983086234404591795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47724058644114979206122393 35793043983086234404591795)
    ·
      refine ⟨53689565974629351606887693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35793043983086234404591795 53689565974629351606887693)
      ·
        refine ⟨20133587240486006852582885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53689565974629351606887693 20133587240486006852582885)
        ·
          refine ⟨3775047607591126284859291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20133587240486006852582885 3775047607591126284859291)
          ·
            refine ⟨5662571411386689427288937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775047607591126284859291 5662571411386689427288937)
            ·
              refine ⟨4246928558540017070466703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5662571411386689427288937 4246928558540017070466703)
              ·
                refine ⟨6370392837810025605700055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4246928558540017070466703 6370392837810025605700055)
                ·
                  refine ⟨9555589256715038408550083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6370392837810025605700055 9555589256715038408550083)
                  ·
                    refine ⟨14333383885072557612825125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9555589256715038408550083 14333383885072557612825125)
                    ·
                      refine ⟨2687509478451104552404711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14333383885072557612825125 2687509478451104552404711)
                      ·
                        rfl

theorem cell23_5233906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_5233906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233906 prefixEnd_5233906 := by exact prefixLift 5233906
  have htrace : WordTrace (prefixWord ++ tailWord_5233906) baseStart_5233906 baseEnd_5233906 := by
    simpa [prefixWord, tailWord_5233906, baseEnd_5233906] using wordTrace_append hprefix tailTrace_5233906
  have hstable : (prefixWord ++ tailWord_5233906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233906).length < 2 ^ (prefixWord ++ tailWord_5233906).sum := by decide
  have hdescent : baseEnd_5233906 < baseStart_5233906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233949 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_5233949 : Nat := 118140960795 + 5233949 * 2 ^ 59
def prefixEnd_5233949 : Nat := 4983230072969 + 3 ^ 40 * 5233949 * 2
def baseEnd_5233949 : Nat := 2687531558119247884167013

theorem tailTrace_5233949 : CollatzResearch.WordTrace tailWord_5233949 prefixEnd_5233949 2687531558119247884167013 := by
  unfold tailWord_5233949
  simp only [CollatzResearch.WordTrace]
  refine ⟨190897802915304135168304901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127265201943536090112203267 190897802915304135168304901)
  ·
    refine ⟨35793338046619525344057169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190897802915304135168304901 35793338046619525344057169)
    ·
      refine ⟨26845003534964644008042877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35793338046619525344057169 26845003534964644008042877)
      ·
        refine ⟨10066876325611741503016079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26845003534964644008042877 10066876325611741503016079)
        ·
          refine ⟨15100314488417612254524119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10066876325611741503016079 15100314488417612254524119)
          ·
            refine ⟨22650471732626418381786179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15100314488417612254524119 22650471732626418381786179)
            ·
              refine ⟨33975707598939627572679269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22650471732626418381786179 33975707598939627572679269)
              ·
                refine ⟨6370445174801180169877363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33975707598939627572679269 6370445174801180169877363)
                ·
                  refine ⟨9555667762201770254816045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6370445174801180169877363 9555667762201770254816045)
                  ·
                    refine ⟨3583375410825663845556017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9555667762201770254816045 3583375410825663845556017)
                    ·
                      refine ⟨2687531558119247884167013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583375410825663845556017 2687531558119247884167013)
                      ·
                        rfl

theorem cell23_5233949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_5233949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233949 prefixEnd_5233949 := by exact prefixLift 5233949
  have htrace : WordTrace (prefixWord ++ tailWord_5233949) baseStart_5233949 baseEnd_5233949 := by
    simpa [prefixWord, tailWord_5233949, baseEnd_5233949] using wordTrace_append hprefix tailTrace_5233949
  have hstable : (prefixWord ++ tailWord_5233949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233949).length < 2 ^ (prefixWord ++ tailWord_5233949).sum := by decide
  have hdescent : baseEnd_5233949 < baseStart_5233949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233978 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_5233978 : Nat := 118140960795 + 5233978 * 2 ^ 59
def prefixEnd_5233978 : Nat := 4983230072969 + 3 ^ 40 * 5233978 * 2
def baseEnd_5233978 : Nat := 2687546449058228270704379

theorem tailTrace_5233978 : CollatzResearch.WordTrace tailWord_5233978 prefixEnd_5233978 2687546449058228270704379 := by
  unfold tailWord_5233978
  simp only [CollatzResearch.WordTrace]
  refine ⟨47724715158049768280277647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127265907088132715414073725 47724715158049768280277647)
  ·
    refine ⟨71587072737074652420416471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47724715158049768280277647 71587072737074652420416471)
    ·
      refine ⟨107380609105611978630624707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71587072737074652420416471 107380609105611978630624707)
      ·
        refine ⟨161070913658417967945937061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107380609105611978630624707 161070913658417967945937061)
        ·
          refine ⟨30200796310953368989863199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161070913658417967945937061 30200796310953368989863199)
          ·
            refine ⟨45301194466430053484794799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30200796310953368989863199 45301194466430053484794799)
            ·
              refine ⟨67951791699645080227192199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45301194466430053484794799 67951791699645080227192199)
              ·
                refine ⟨101927687549467620340788299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67951791699645080227192199 101927687549467620340788299)
                ·
                  refine ⟨152891531324201430511182449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101927687549467620340788299 152891531324201430511182449)
                  ·
                    refine ⟨114668648493151072883386837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152891531324201430511182449 114668648493151072883386837)
                    ·
                      refine ⟨2687546449058228270704379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114668648493151072883386837 2687546449058228270704379)
                      ·
                        rfl

theorem cell23_5233978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_5233978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233978 prefixEnd_5233978 := by exact prefixLift 5233978
  have htrace : WordTrace (prefixWord ++ tailWord_5233978) baseStart_5233978 baseEnd_5233978 := by
    simpa [prefixWord, tailWord_5233978, baseEnd_5233978] using wordTrace_append hprefix tailTrace_5233978
  have hstable : (prefixWord ++ tailWord_5233978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233978).length < 2 ^ (prefixWord ++ tailWord_5233978).sum := by decide
  have hdescent : baseEnd_5233978 < baseStart_5233978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5233996 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 2, 2, 2]
def baseStart_5233996 : Nat := 118140960795 + 5233996 * 2 ^ 59
def prefixEnd_5233996 : Nat := 4983230072969 + 3 ^ 40 * 5233996 * 2
def baseEnd_5233996 : Nat := 2687555691710009200279297

theorem tailTrace_5233996 : CollatzResearch.WordTrace tailWord_5233996 prefixEnd_5233996 2687555691710009200279297 := by
  unfold tailWord_5233996
  simp only [CollatzResearch.WordTrace]
  refine ⟨95449758573066931097632921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127266344764089241463510561 95449758573066931097632921)
  ·
    refine ⟨71587318929800198323224691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95449758573066931097632921 71587318929800198323224691)
    ·
      refine ⟨107380978394700297484837037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71587318929800198323224691 107380978394700297484837037)
      ·
        refine ⟨40267866898012611556813889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107380978394700297484837037 40267866898012611556813889)
        ·
          refine ⟨30200900173509458667610417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40267866898012611556813889 30200900173509458667610417)
          ·
            refine ⟨22650675130132094000707813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30200900173509458667610417 22650675130132094000707813)
            ·
              refine ⟨4247001586899767625132715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22650675130132094000707813 4247001586899767625132715)
              ·
                refine ⟨6370502380349651437699073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4247001586899767625132715 6370502380349651437699073)
                ·
                  refine ⟨4777876785262238578274305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6370502380349651437699073 4777876785262238578274305)
                  ·
                    refine ⟨3583407588946678933705729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4777876785262238578274305 3583407588946678933705729)
                    ·
                      refine ⟨2687555691710009200279297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583407588946678933705729 2687555691710009200279297)
                      ·
                        rfl

theorem cell23_5233996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_5233996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5233996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5233996 prefixEnd_5233996 := by exact prefixLift 5233996
  have htrace : WordTrace (prefixWord ++ tailWord_5233996) baseStart_5233996 baseEnd_5233996 := by
    simpa [prefixWord, tailWord_5233996, baseEnd_5233996] using wordTrace_append hprefix tailTrace_5233996
  have hstable : (prefixWord ++ tailWord_5233996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5233996).length < 2 ^ (prefixWord ++ tailWord_5233996).sum := by decide
  have hdescent : baseEnd_5233996 < baseStart_5233996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5233996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234008 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_5234008 : Nat := 118140960795 + 5234008 * 2 ^ 59
def prefixEnd_5234008 : Nat := 4983230072969 + 3 ^ 40 * 5234008 * 2
def baseEnd_5234008 : Nat := 2687561853477863153329241

theorem tailTrace_5234008 : CollatzResearch.WordTrace tailWord_5234008 prefixEnd_5234008 2687561853477863153329241 := by
  unfold tailWord_5234008
  simp only [CollatzResearch.WordTrace]
  refine ⟨95449977411045194122351339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127266636548060258829801785 95449977411045194122351339)
  ·
    refine ⟨143174966116567791183527009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95449977411045194122351339 143174966116567791183527009)
    ·
      refine ⟨107381224587425843387645257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143174966116567791183527009 107381224587425843387645257)
      ·
        refine ⟨80535918440569382540733943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107381224587425843387645257 80535918440569382540733943)
        ·
          refine ⟨120803877660854073811100915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80535918440569382540733943 120803877660854073811100915)
          ·
            refine ⟨181205816491281110716651373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120803877660854073811100915 181205816491281110716651373)
            ·
              refine ⟨67952181184230416518744265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181205816491281110716651373 67952181184230416518744265)
              ·
                refine ⟨50964135888172812389058199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67952181184230416518744265 50964135888172812389058199)
                ·
                  refine ⟨76446203832259218583587299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50964135888172812389058199 76446203832259218583587299)
                  ·
                    refine ⟨114669305748388827875380949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76446203832259218583587299 114669305748388827875380949)
                    ·
                      refine ⟨2687561853477863153329241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114669305748388827875380949 2687561853477863153329241)
                      ·
                        rfl

theorem cell23_5234008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_5234008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234008 prefixEnd_5234008 := by exact prefixLift 5234008
  have htrace : WordTrace (prefixWord ++ tailWord_5234008) baseStart_5234008 baseEnd_5234008 := by
    simpa [prefixWord, tailWord_5234008, baseEnd_5234008] using wordTrace_append hprefix tailTrace_5234008
  have hstable : (prefixWord ++ tailWord_5234008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234008).length < 2 ^ (prefixWord ++ tailWord_5234008).sum := by decide
  have hdescent : baseEnd_5234008 < baseStart_5234008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234013 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5234013 : Nat := 118140960795 + 5234013 * 2 ^ 59
def prefixEnd_5234013 : Nat := 4983230072969 + 3 ^ 40 * 5234013 * 2
def baseEnd_5234013 : Nat := 2687564420881135633766719

theorem tailTrace_5234013 : CollatzResearch.WordTrace tailWord_5234013 prefixEnd_5234013 2687564420881135633766719 := by
  unfold tailWord_5234013
  simp only [CollatzResearch.WordTrace]
  refine ⟨190900137187072274098634693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127266758124714849399089795 190900137187072274098634693)
  ·
    refine ⟨35793775722576051393494005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190900137187072274098634693 35793775722576051393494005)
    ·
      refine ⟨3355666473991504818140063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35793775722576051393494005 3355666473991504818140063)
      ·
        refine ⟨5033499710987257227210095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3355666473991504818140063 5033499710987257227210095)
        ·
          refine ⟨7550249566480885840815143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033499710987257227210095 7550249566480885840815143)
          ·
            refine ⟨11325374349721328761222715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7550249566480885840815143 11325374349721328761222715)
            ·
              refine ⟨16988061524581993141834073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11325374349721328761222715 16988061524581993141834073)
              ·
                refine ⟨12741046143436494856375555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16988061524581993141834073 12741046143436494856375555)
                ·
                  refine ⟨19111569215154742284563333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12741046143436494856375555 19111569215154742284563333)
                  ·
                    refine ⟨3583419227841514178355625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19111569215154742284563333 3583419227841514178355625)
                    ·
                      refine ⟨2687564420881135633766719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583419227841514178355625 2687564420881135633766719)
                      ·
                        rfl

theorem cell23_5234013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5234013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234013 prefixEnd_5234013 := by exact prefixLift 5234013
  have htrace : WordTrace (prefixWord ++ tailWord_5234013) baseStart_5234013 baseEnd_5234013 := by
    simpa [prefixWord, tailWord_5234013, baseEnd_5234013] using wordTrace_append hprefix tailTrace_5234013
  have hstable : (prefixWord ++ tailWord_5234013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234013).length < 2 ^ (prefixWord ++ tailWord_5234013).sum := by decide
  have hdescent : baseEnd_5234013 < baseStart_5234013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234046 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5234046 : Nat := 118140960795 + 5234046 * 2 ^ 59
def prefixEnd_5234046 : Nat := 4983230072969 + 3 ^ 40 * 5234046 * 2
def baseEnd_5234046 : Nat := 2687581365742734004654067

theorem tailTrace_5234046 : CollatzResearch.WordTrace tailWord_5234046 prefixEnd_5234046 2687581365742734004654067 := by
  unfold tailWord_5234046
  simp only [CollatzResearch.WordTrace]
  refine ⟨23862667599494090091823249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127267560530635147156390661 23862667599494090091823249)
  ·
    refine ⟨17897000699620567568867437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23862667599494090091823249 17897000699620567568867437)
    ·
      refine ⟨6711375262357712838325289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17897000699620567568867437 6711375262357712838325289)
      ·
        refine ⟨5033531446768284628743967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6711375262357712838325289 5033531446768284628743967)
        ·
          refine ⟨7550297170152426943115951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033531446768284628743967 7550297170152426943115951)
          ·
            refine ⟨11325445755228640414673927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7550297170152426943115951 11325445755228640414673927)
            ·
              refine ⟨16988168632842960622010891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11325445755228640414673927 16988168632842960622010891)
              ·
                refine ⟨25482252949264440933016337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16988168632842960622010891 25482252949264440933016337)
                ·
                  refine ⟨19111689711948330699762253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25482252949264440933016337 19111689711948330699762253)
                  ·
                    refine ⟨7166883641980624012410845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19111689711948330699762253 7166883641980624012410845)
                    ·
                      refine ⟨2687581365742734004654067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7166883641980624012410845 2687581365742734004654067)
                      ·
                        rfl

theorem cell23_5234046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5234046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234046 prefixEnd_5234046 := by exact prefixLift 5234046
  have htrace : WordTrace (prefixWord ++ tailWord_5234046) baseStart_5234046 baseEnd_5234046 := by
    simpa [prefixWord, tailWord_5234046, baseEnd_5234046] using wordTrace_append hprefix tailTrace_5234046
  have hstable : (prefixWord ++ tailWord_5234046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234046).length < 2 ^ (prefixWord ++ tailWord_5234046).sum := by decide
  have hdescent : baseEnd_5234046 < baseStart_5234046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234052 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_5234052 : Nat := 118140960795 + 5234052 * 2 ^ 59
def prefixEnd_5234052 : Nat := 4983230072969 + 3 ^ 40 * 5234052 * 2
def baseEnd_5234052 : Nat := 2687584446626660981179039

theorem tailTrace_5234052 : CollatzResearch.WordTrace tailWord_5234052 prefixEnd_5234052 2687584446626660981179039 := by
  unfold tailWord_5234052
  simp only [CollatzResearch.WordTrace]
  refine ⟨95450779816965491879652205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127267706422620655839536273 95450779816965491879652205)
  ·
    refine ⟨35794042431362059454869577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95450779816965491879652205 35794042431362059454869577)
    ·
      refine ⟨26845531823521544591152183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35794042431362059454869577 26845531823521544591152183)
      ·
        refine ⟨40268297735282316886728275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26845531823521544591152183 40268297735282316886728275)
        ·
          refine ⟨60402446602923475330092413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40268297735282316886728275 60402446602923475330092413)
          ·
            refine ⟨22650917476096303248784655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60402446602923475330092413 22650917476096303248784655)
            ·
              refine ⟨33976376214144454873176983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22650917476096303248784655 33976376214144454873176983)
              ·
                refine ⟨50964564321216682309765475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33976376214144454873176983 50964564321216682309765475)
                ·
                  refine ⟨76446846481825023464648213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50964564321216682309765475 76446846481825023464648213)
                  ·
                    refine ⟨3583445928835547974905385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76446846481825023464648213 3583445928835547974905385)
                    ·
                      refine ⟨2687584446626660981179039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583445928835547974905385 2687584446626660981179039)
                      ·
                        rfl

theorem cell23_5234052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_5234052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234052 prefixEnd_5234052 := by exact prefixLift 5234052
  have htrace : WordTrace (prefixWord ++ tailWord_5234052) baseStart_5234052 baseEnd_5234052 := by
    simpa [prefixWord, tailWord_5234052, baseEnd_5234052] using wordTrace_append hprefix tailTrace_5234052
  have hstable : (prefixWord ++ tailWord_5234052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234052).length < 2 ^ (prefixWord ++ tailWord_5234052).sum := by decide
  have hdescent : baseEnd_5234052 < baseStart_5234052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234066 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_5234066 : Nat := 118140960795 + 5234066 * 2 ^ 59
def prefixEnd_5234066 : Nat := 4983230072969 + 3 ^ 40 * 5234066 * 2
def baseEnd_5234066 : Nat := 895863878451941308801325

theorem tailTrace_5234066 : CollatzResearch.WordTrace tailWord_5234066 prefixEnd_5234066 895863878451941308801325 := by
  unfold tailWord_5234066
  simp only [CollatzResearch.WordTrace]
  refine ⟨47725517563970066037578513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127268046837253509433542701 47725517563970066037578513)
  ·
    refine ⟨35794138172977549528183885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47725517563970066037578513 35794138172977549528183885)
    ·
      refine ⟨13422801814866581073068957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35794138172977549528183885 13422801814866581073068957)
      ·
        refine ⟨5033550680574967902400859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13422801814866581073068957 5033550680574967902400859)
        ·
          refine ⟨7550326020862451853601289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5033550680574967902400859 7550326020862451853601289)
          ·
            refine ⟨5662744515646838890200967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7550326020862451853601289 5662744515646838890200967)
            ·
              refine ⟨8494116773470258335301451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662744515646838890200967 8494116773470258335301451)
              ·
                refine ⟨12741175160205387502952177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8494116773470258335301451 12741175160205387502952177)
                ·
                  refine ⟨9555881370154040627214133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12741175160205387502952177 9555881370154040627214133)
                  ·
                    refine ⟨895863878451941308801325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9555881370154040627214133 895863878451941308801325)
                    ·
                      rfl

theorem cell23_5234066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_5234066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234066 prefixEnd_5234066 := by exact prefixLift 5234066
  have htrace : WordTrace (prefixWord ++ tailWord_5234066) baseStart_5234066 baseEnd_5234066 := by
    simpa [prefixWord, tailWord_5234066, baseEnd_5234066] using wordTrace_append hprefix tailTrace_5234066
  have hstable : (prefixWord ++ tailWord_5234066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234066).length < 2 ^ (prefixWord ++ tailWord_5234066).sum := by decide
  have hdescent : baseEnd_5234066 < baseStart_5234066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234079 : List Nat := [1, 1, 2, 5, 1, 2, 1, 5, 1, 4]
def baseStart_5234079 : Nat := 118140960795 + 5234079 * 2 ^ 59
def prefixEnd_5234079 : Nat := 4983230072969 + 3 ^ 40 * 5234079 * 2
def baseEnd_5234079 : Nat := 895866103534777458513805

theorem tailTrace_5234079 : CollatzResearch.WordTrace tailWord_5234079 prefixEnd_5234079 895866103534777458513805 := by
  unfold tailWord_5234079
  simp only [CollatzResearch.WordTrace]
  refine ⟨190902544404833167370537291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127268362936555444913691527 190902544404833167370537291)
  ·
    refine ⟨286353816607249751055805937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190902544404833167370537291 286353816607249751055805937)
    ·
      refine ⟨214765362455437313291854453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286353816607249751055805937 214765362455437313291854453)
      ·
        refine ⟨20134252730197248121111355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214765362455437313291854453 20134252730197248121111355)
        ·
          refine ⟨30201379095295872181667033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20134252730197248121111355 30201379095295872181667033)
          ·
            refine ⟨22651034321471904136250275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30201379095295872181667033 22651034321471904136250275)
            ·
              refine ⟨33976551482207856204375413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22651034321471904136250275 33976551482207856204375413)
              ·
                refine ⟨3185301701456986519160195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33976551482207856204375413 3185301701456986519160195)
                ·
                  refine ⟨4777952552185479778740293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185301701456986519160195 4777952552185479778740293)
                  ·
                    refine ⟨895866103534777458513805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4777952552185479778740293 895866103534777458513805)
                    ·
                      rfl

theorem cell23_5234079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 1, 4].length) (baseStart_5234079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234079 prefixEnd_5234079 := by exact prefixLift 5234079
  have htrace : WordTrace (prefixWord ++ tailWord_5234079) baseStart_5234079 baseEnd_5234079 := by
    simpa [prefixWord, tailWord_5234079, baseEnd_5234079] using wordTrace_append hprefix tailTrace_5234079
  have hstable : (prefixWord ++ tailWord_5234079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234079).length < 2 ^ (prefixWord ++ tailWord_5234079).sum := by decide
  have hdescent : baseEnd_5234079 < baseStart_5234079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234112 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 1, 5, 2]
def baseStart_5234112 : Nat := 118140960795 + 5234112 * 2 ^ 59
def prefixEnd_5234112 : Nat := 4983230072969 + 3 ^ 40 * 5234112 * 2
def baseEnd_5234112 : Nat := 2687615255465930746428763

theorem tailTrace_5234112 : CollatzResearch.WordTrace tailWord_5234112 prefixEnd_5234112 2687615255465930746428763 := by
  unfold tailWord_5234112
  simp only [CollatzResearch.WordTrace]
  refine ⟨95451874006856807003244295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127269165342475742670992393 95451874006856807003244295)
  ·
    refine ⟨143177811010285210504866443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95451874006856807003244295 143177811010285210504866443)
    ·
      refine ⟨214766716515427815757299665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143177811010285210504866443 214766716515427815757299665)
      ·
        refine ⟨161075037386570861817974749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214766716515427815757299665 161075037386570861817974749)
        ·
          refine ⟨60403139019964073181740531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161075037386570861817974749 60403139019964073181740531)
          ·
            refine ⟨90604708529946109772610797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60403139019964073181740531 90604708529946109772610797)
            ·
              refine ⟨33976765698729791164729049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90604708529946109772610797 33976765698729791164729049)
              ·
                refine ⟨25482574274047343373546787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33976765698729791164729049 25482574274047343373546787)
                ·
                  refine ⟨38223861411071015060320181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25482574274047343373546787 38223861411071015060320181)
                  ·
                    refine ⟨3583487007287907661905017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38223861411071015060320181 3583487007287907661905017)
                    ·
                      refine ⟨2687615255465930746428763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583487007287907661905017 2687615255465930746428763)
                      ·
                        rfl

theorem cell23_5234112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_5234112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234112 prefixEnd_5234112 := by exact prefixLift 5234112
  have htrace : WordTrace (prefixWord ++ tailWord_5234112) baseStart_5234112 baseEnd_5234112 := by
    simpa [prefixWord, tailWord_5234112, baseEnd_5234112] using wordTrace_append hprefix tailTrace_5234112
  have hstable : (prefixWord ++ tailWord_5234112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234112).length < 2 ^ (prefixWord ++ tailWord_5234112).sum := by decide
  have hdescent : baseEnd_5234112 < baseStart_5234112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234122 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_5234122 : Nat := 118140960795 + 5234122 * 2 ^ 59
def prefixEnd_5234122 : Nat := 4983230072969 + 3 ^ 40 * 5234122 * 2
def baseEnd_5234122 : Nat := 895873463424158569101239

theorem tailTrace_5234122 : CollatzResearch.WordTrace tailWord_5234122 prefixEnd_5234122 895873463424158569101239 := by
  unfold tailWord_5234122
  simp only [CollatzResearch.WordTrace]
  refine ⟨47726028185919346428588155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127269408495784923809568413 47726028185919346428588155)
  ·
    refine ⟨71589042278879019642882233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47726028185919346428588155 71589042278879019642882233)
    ·
      refine ⟨53691781709159264732161675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71589042278879019642882233 53691781709159264732161675)
      ·
        refine ⟨80537672563738897098242513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53691781709159264732161675 80537672563738897098242513)
        ·
          refine ⟨60403254422804172823681885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80537672563738897098242513 60403254422804172823681885)
          ·
            refine ⟨22651220408551564808880707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60403254422804172823681885 22651220408551564808880707)
            ·
              refine ⟨33976830612827347213321061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22651220408551564808880707 33976830612827347213321061)
              ·
                refine ⟨6370655739905127602497699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33976830612827347213321061 6370655739905127602497699)
                ·
                  refine ⟨9555983609857691403746549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6370655739905127602497699 9555983609857691403746549)
                  ·
                    refine ⟨895873463424158569101239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9555983609857691403746549 895873463424158569101239)
                    ·
                      rfl

theorem cell23_5234122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_5234122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234122 prefixEnd_5234122 := by exact prefixLift 5234122
  have htrace : WordTrace (prefixWord ++ tailWord_5234122) baseStart_5234122 baseEnd_5234122 := by
    simpa [prefixWord, tailWord_5234122, baseEnd_5234122] using wordTrace_append hprefix tailTrace_5234122
  have hstable : (prefixWord ++ tailWord_5234122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234122).length < 2 ^ (prefixWord ++ tailWord_5234122).sum := by decide
  have hdescent : baseEnd_5234122 < baseStart_5234122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234135 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 1, 6]
def baseStart_5234135 : Nat := 118140960795 + 5234135 * 2 ^ 59
def prefixEnd_5234135 : Nat := 4983230072969 + 3 ^ 40 * 5234135 * 2
def baseEnd_5234135 : Nat := 895875688506994718813719

theorem tailTrace_5234135 : CollatzResearch.WordTrace tailWord_5234135 prefixEnd_5234135 895875688506994718813719 := by
  unfold tailWord_5234135
  simp only [CollatzResearch.WordTrace]
  refine ⟨190904586892630288934575859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127269724595086859289717239 190904586892630288934575859)
  ·
    refine ⟨286356880338945433401863789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190904586892630288934575859 286356880338945433401863789)
    ·
      refine ⟨107383830127104537525698921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286356880338945433401863789 107383830127104537525698921)
      ·
        refine ⟨80537872595328403144274191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107383830127104537525698921 80537872595328403144274191)
        ·
          refine ⟨120806808892992604716411287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80537872595328403144274191 120806808892992604716411287)
          ·
            refine ⟨181210213339488907074616931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120806808892992604716411287 181210213339488907074616931)
            ·
              refine ⟨271815320009233360611925397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181210213339488907074616931 271815320009233360611925397)
              ·
                refine ⟨12741343125432813778684003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 271815320009233360611925397 12741343125432813778684003)
                ·
                  refine ⟨19112014688149220668026005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12741343125432813778684003 19112014688149220668026005)
                  ·
                    refine ⟨895875688506994718813719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19112014688149220668026005 895875688506994718813719)
                    ·
                      rfl

theorem cell23_5234135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_5234135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234135 prefixEnd_5234135 := by exact prefixLift 5234135
  have htrace : WordTrace (prefixWord ++ tailWord_5234135) baseStart_5234135 baseEnd_5234135 := by
    simpa [prefixWord, tailWord_5234135, baseEnd_5234135] using wordTrace_append hprefix tailTrace_5234135
  have hstable : (prefixWord ++ tailWord_5234135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234135).length < 2 ^ (prefixWord ++ tailWord_5234135).sum := by decide
  have hdescent : baseEnd_5234135 < baseStart_5234135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234136 : List Nat := [2, 1, 2, 2, 2, 1, 5, 3, 1, 1, 3]
def baseStart_5234136 : Nat := 118140960795 + 5234136 * 2 ^ 59
def prefixEnd_5234136 : Nat := 4983230072969 + 3 ^ 40 * 5234136 * 2
def baseEnd_5234136 : Nat := 2687627579001638652528653

theorem tailTrace_5234136 : CollatzResearch.WordTrace tailWord_5234136 prefixEnd_5234136 2687627579001638652528653 := by
  unfold tailWord_5234136
  simp only [CollatzResearch.WordTrace]
  refine ⟨95452311682813333052681131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127269748910417777403574841 95452311682813333052681131)
  ·
    refine ⟨143178467524219999579021697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95452311682813333052681131 143178467524219999579021697)
    ·
      refine ⟨107383850643164999684266273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143178467524219999579021697 107383850643164999684266273)
      ·
        refine ⟨80537887982373749763199705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107383850643164999684266273 80537887982373749763199705)
        ·
          refine ⟨60403415986780312322399779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80537887982373749763199705 60403415986780312322399779)
          ·
            refine ⟨90605123980170468483599669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60403415986780312322399779 90605123980170468483599669)
            ·
              refine ⟨8494230373140981420337469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90605123980170468483599669 8494230373140981420337469)
              ·
                refine ⟨3185336389927868032626551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8494230373140981420337469 3185336389927868032626551)
                ·
                  refine ⟨4778004584891802048939827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185336389927868032626551 4778004584891802048939827)
                  ·
                    refine ⟨7167006877337703073409741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4778004584891802048939827 7167006877337703073409741)
                    ·
                      refine ⟨2687627579001638652528653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7167006877337703073409741 2687627579001638652528653)
                      ·
                        rfl

theorem cell23_5234136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_5234136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234136 prefixEnd_5234136 := by exact prefixLift 5234136
  have htrace : WordTrace (prefixWord ++ tailWord_5234136) baseStart_5234136 baseEnd_5234136 := by
    simpa [prefixWord, tailWord_5234136, baseEnd_5234136] using wordTrace_append hprefix tailTrace_5234136
  have hstable : (prefixWord ++ tailWord_5234136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234136).length < 2 ^ (prefixWord ++ tailWord_5234136).sum := by decide
  have hdescent : baseEnd_5234136 < baseStart_5234136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234152 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 4, 4]
def baseStart_5234152 : Nat := 118140960795 + 5234152 * 2 ^ 59
def prefixEnd_5234152 : Nat := 4983230072969 + 3 ^ 40 * 5234152 * 2
def baseEnd_5234152 : Nat := 895878598230703529976193

theorem tailTrace_5234152 : CollatzResearch.WordTrace tailWord_5234152 prefixEnd_5234152 895878598230703529976193 := by
  unfold tailWord_5234152
  simp only [CollatzResearch.WordTrace]
  refine ⟨95452603466784350418972355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127270137955712467225296473 95452603466784350418972355)
  ·
    refine ⟨143178905200176525628458533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95452603466784350418972355 143178905200176525628458533)
    ·
      refine ⟨26846044725033098555335975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143178905200176525628458533 26846044725033098555335975)
      ·
        refine ⟨40269067087549647833003963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26846044725033098555335975 40269067087549647833003963)
        ·
          refine ⟨60403600631324471749505945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40269067087549647833003963 60403600631324471749505945)
          ·
            refine ⟨45302700473493353812129459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60403600631324471749505945 45302700473493353812129459)
            ·
              refine ⟨67954050710240030718194189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45302700473493353812129459 67954050710240030718194189)
              ·
                refine ⟨25482769016340011519322821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67954050710240030718194189 25482769016340011519322821)
                ·
                  refine ⟨4778019190563752159873029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25482769016340011519322821 4778019190563752159873029)
                  ·
                    refine ⟨895878598230703529976193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4778019190563752159873029 895878598230703529976193)
                    ·
                      rfl

theorem cell23_5234152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_5234152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234152 prefixEnd_5234152 := by exact prefixLift 5234152
  have htrace : WordTrace (prefixWord ++ tailWord_5234152) baseStart_5234152 baseEnd_5234152 := by
    simpa [prefixWord, tailWord_5234152, baseEnd_5234152] using wordTrace_append hprefix tailTrace_5234152
  have hstable : (prefixWord ++ tailWord_5234152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234152).length < 2 ^ (prefixWord ++ tailWord_5234152).sum := by decide
  have hdescent : baseEnd_5234152 < baseStart_5234152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234155 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 4]
def baseStart_5234155 : Nat := 118140960795 + 5234155 * 2 ^ 59
def prefixEnd_5234155 : Nat := 4983230072969 + 3 ^ 40 * 5234155 * 2
def baseEnd_5234155 : Nat := 2687637335134074078191065

theorem tailTrace_5234155 : CollatzResearch.WordTrace tailWord_5234155 prefixEnd_5234155 2687637335134074078191065 := by
  unfold tailWord_5234155
  simp only [CollatzResearch.WordTrace]
  refine ⟨190905316352557832350303919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127270210901705221566869279 190905316352557832350303919)
  ·
    refine ⟨286357974528836748525455879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190905316352557832350303919 286357974528836748525455879)
    ·
      refine ⟨429536961793255122788183819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286357974528836748525455879 429536961793255122788183819)
      ·
        refine ⟨644305442689882684182275729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429536961793255122788183819 644305442689882684182275729)
        ·
          refine ⟨483229082017412013136706797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644305442689882684182275729 483229082017412013136706797)
          ·
            refine ⟨181210905756529504926265049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 483229082017412013136706797 181210905756529504926265049)
            ·
              refine ⟨135908179317397128694698787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181210905756529504926265049 135908179317397128694698787)
              ·
                refine ⟨203862268976095693042048181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135908179317397128694698787 203862268976095693042048181)
                ·
                  refine ⟨19112087716508971222692017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203862268976095693042048181 19112087716508971222692017)
                  ·
                    refine ⟨14334065787381728417019013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19112087716508971222692017 14334065787381728417019013)
                    ·
                      refine ⟨2687637335134074078191065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14334065787381728417019013 2687637335134074078191065)
                      ·
                        rfl

theorem cell23_5234155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 4].length) (baseStart_5234155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234155 prefixEnd_5234155 := by exact prefixLift 5234155
  have htrace : WordTrace (prefixWord ++ tailWord_5234155) baseStart_5234155 baseEnd_5234155 := by
    simpa [prefixWord, tailWord_5234155, baseEnd_5234155] using wordTrace_append hprefix tailTrace_5234155
  have hstable : (prefixWord ++ tailWord_5234155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234155).length < 2 ^ (prefixWord ++ tailWord_5234155).sum := by decide
  have hdescent : baseEnd_5234155 < baseStart_5234155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234210 : List Nat := [3, 3, 1, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_5234210 : Nat := 118140960795 + 5234210 * 2 ^ 59
def prefixEnd_5234210 : Nat := 4983230072969 + 3 ^ 40 * 5234210 * 2
def baseEnd_5234210 : Nat := 2687665576570071363003313

theorem tailTrace_5234210 : CollatzResearch.WordTrace tailWord_5234210 prefixEnd_5234210 2687665576570071363003313 := by
  unfold tailWord_5234210
  simp only [CollatzResearch.WordTrace]
  refine ⟨47726830591839644185889021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127271548244905717829037389 47726830591839644185889021)
  ·
    refine ⟨17897561471939866569708383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47726830591839644185889021 17897561471939866569708383)
    ·
      refine ⟨26846342207909799854562575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17897561471939866569708383 26846342207909799854562575)
      ·
        refine ⟨40269513311864699781843863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26846342207909799854562575 40269513311864699781843863)
        ·
          refine ⟨60404269967797049672765795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40269513311864699781843863 60404269967797049672765795)
          ·
            refine ⟨90606404951695574509148693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60404269967797049672765795 90606404951695574509148693)
            ·
              refine ⟨4247175232110730055116345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90606404951695574509148693 4247175232110730055116345)
              ·
                refine ⟨3185381424083047541337259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247175232110730055116345 3185381424083047541337259)
                ·
                  refine ⟨4778072136124571312005889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185381424083047541337259 4778072136124571312005889)
                  ·
                    refine ⟨3583554102093428484004417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4778072136124571312005889 3583554102093428484004417)
                    ·
                      refine ⟨2687665576570071363003313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583554102093428484004417 2687665576570071363003313)
                      ·
                        rfl

theorem cell23_5234210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_5234210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234210 prefixEnd_5234210 := by exact prefixLift 5234210
  have htrace : WordTrace (prefixWord ++ tailWord_5234210) baseStart_5234210 baseEnd_5234210 := by
    simpa [prefixWord, tailWord_5234210, baseEnd_5234210] using wordTrace_append hprefix tailTrace_5234210
  have hstable : (prefixWord ++ tailWord_5234210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234210).length < 2 ^ (prefixWord ++ tailWord_5234210).sum := by decide
  have hdescent : baseEnd_5234210 < baseStart_5234210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234216 : List Nat := [2, 1, 5, 2, 3, 1, 1, 8]
def baseStart_5234216 : Nat := 118140960795 + 5234216 * 2 ^ 59
def prefixEnd_5234216 : Nat := 4983230072969 + 3 ^ 40 * 5234216 * 2
def baseEnd_5234216 : Nat := 99543283609407345908455

theorem tailTrace_5234216 : CollatzResearch.WordTrace tailWord_5234216 prefixEnd_5234216 99543283609407345908455 := by
  unfold tailWord_5234216
  simp only [CollatzResearch.WordTrace]
  refine ⟨95453770602668419884137251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127271694136891226512183001 95453770602668419884137251)
  ·
    refine ⟨143180655904002629826205877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95453770602668419884137251 143180655904002629826205877)
    ·
      refine ⟨13423186491000246546206801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143180655904002629826205877 13423186491000246546206801)
      ·
        refine ⟨10067389868250184909655101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13423186491000246546206801 10067389868250184909655101)
        ·
          refine ⟨3775271200593819341120663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10067389868250184909655101 3775271200593819341120663)
          ·
            refine ⟨5662906800890729011680995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775271200593819341120663 5662906800890729011680995)
            ·
              refine ⟨8494360201336093517521493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5662906800890729011680995 8494360201336093517521493)
              ·
                refine ⟨99543283609407345908455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8494360201336093517521493 99543283609407345908455)
                ·
                  rfl

theorem cell23_5234216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 8].length) (baseStart_5234216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234216 prefixEnd_5234216 := by exact prefixLift 5234216
  have htrace : WordTrace (prefixWord ++ tailWord_5234216) baseStart_5234216 baseEnd_5234216 := by
    simpa [prefixWord, tailWord_5234216, baseEnd_5234216] using wordTrace_append hprefix tailTrace_5234216
  have hstable : (prefixWord ++ tailWord_5234216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234216).length < 2 ^ (prefixWord ++ tailWord_5234216).sum := by decide
  have hdescent : baseEnd_5234216 < baseStart_5234216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234255 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 11]
def baseStart_5234255 : Nat := 118140960795 + 5234255 * 2 ^ 59
def prefixEnd_5234255 : Nat := 4983230072969 + 3 ^ 40 * 5234255 * 2
def baseEnd_5234255 : Nat := 298632075911058187437845

theorem tailTrace_5234255 : CollatzResearch.WordTrace tailWord_5234255 prefixEnd_5234255 298632075911058187437845 := by
  unfold tailWord_5234255
  simp only [CollatzResearch.WordTrace]
  refine ⟨190908963652195549428944219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127272642434797032952629479 190908963652195549428944219)
  ·
    refine ⟨286363445478293324143416329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190908963652195549428944219 286363445478293324143416329)
    ·
      refine ⟨214772584108719993107562247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286363445478293324143416329 214772584108719993107562247)
      ·
        refine ⟨322158876163079989661343371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214772584108719993107562247 322158876163079989661343371)
        ·
          refine ⟨483238314244619984492015057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322158876163079989661343371 483238314244619984492015057)
          ·
            refine ⟨362428735683464988369011293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483238314244619984492015057 362428735683464988369011293)
            ·
              refine ⟨135910775881299370638379235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362428735683464988369011293 135910775881299370638379235)
              ·
                refine ⟨203866163821949055957568853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135910775881299370638379235 203866163821949055957568853)
                ·
                  refine ⟨298632075911058187437845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 203866163821949055957568853 298632075911058187437845)
                  ·
                    rfl

theorem cell23_5234255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 11].length) (baseStart_5234255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234255 prefixEnd_5234255 := by exact prefixLift 5234255
  have htrace : WordTrace (prefixWord ++ tailWord_5234255) baseStart_5234255 baseEnd_5234255 := by
    simpa [prefixWord, tailWord_5234255, baseEnd_5234255] using wordTrace_append hprefix tailTrace_5234255
  have hstable : (prefixWord ++ tailWord_5234255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234255).length < 2 ^ (prefixWord ++ tailWord_5234255).sum := by decide
  have hdescent : baseEnd_5234255 < baseStart_5234255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234339 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 1, 6, 2]
def baseStart_5234339 : Nat := 118140960795 + 5234339 * 2 ^ 59
def prefixEnd_5234339 : Nat := 4983230072969 + 3 ^ 40 * 5234339 * 2
def baseEnd_5234339 : Nat := 2687731815574501358290219

theorem tailTrace_5234339 : CollatzResearch.WordTrace tailWord_5234339 prefixEnd_5234339 2687731815574501358290219 := by
  unfold tailWord_5234339
  simp only [CollatzResearch.WordTrace]
  refine ⟨190912027383891231775002071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127274684922594154516668047 190912027383891231775002071)
  ·
    refine ⟨286368041075836847662503107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190912027383891231775002071 286368041075836847662503107)
    ·
      refine ⟨429552061613755271493754661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286368041075836847662503107 429552061613755271493754661)
      ·
        refine ⟨80541011552579113405078999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 429552061613755271493754661 80541011552579113405078999)
        ·
          refine ⟨120811517328868670107618499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80541011552579113405078999 120811517328868670107618499)
          ·
            refine ⟨181217275993303005161427749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120811517328868670107618499 181217275993303005161427749)
            ·
              refine ⟨33978239248744313467767703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181217275993303005161427749 33978239248744313467767703)
              ·
                refine ⟨50967358873116470201651555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33978239248744313467767703 50967358873116470201651555)
                ·
                  refine ⟨76451038309674705302477333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50967358873116470201651555 76451038309674705302477333)
                  ·
                    refine ⟨3583642420766001811053625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76451038309674705302477333 3583642420766001811053625)
                    ·
                      refine ⟨2687731815574501358290219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583642420766001811053625 2687731815574501358290219)
                      ·
                        rfl

theorem cell23_5234339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_5234339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234339 prefixEnd_5234339 := by exact prefixLift 5234339
  have htrace : WordTrace (prefixWord ++ tailWord_5234339) baseStart_5234339 baseEnd_5234339 := by
    simpa [prefixWord, tailWord_5234339, baseEnd_5234339] using wordTrace_append hprefix tailTrace_5234339
  have hstable : (prefixWord ++ tailWord_5234339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234339).length < 2 ^ (prefixWord ++ tailWord_5234339).sum := by decide
  have hdescent : baseEnd_5234339 < baseStart_5234339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234352 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_5234352 : Nat := 118140960795 + 5234352 * 2 ^ 59
def prefixEnd_5234352 : Nat := 4983230072969 + 3 ^ 40 * 5234352 * 2
def baseEnd_5234352 : Nat := 2687738490823009807427659

theorem tailTrace_5234352 : CollatzResearch.WordTrace tailWord_5234352 prefixEnd_5234352 2687738490823009807427659 := by
  unfold tailWord_5234352
  simp only [CollatzResearch.WordTrace]
  refine ⟨95456250766422067497612655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127275001021896089996816873 95456250766422067497612655)
  ·
    refine ⟨143184376149633101246418983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95456250766422067497612655 143184376149633101246418983)
    ·
      refine ⟨214776564224449651869628475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143184376149633101246418983 214776564224449651869628475)
      ·
        refine ⟨322164846336674477804442713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214776564224449651869628475 322164846336674477804442713)
        ·
          refine ⟨241623634752505858353332035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322164846336674477804442713 241623634752505858353332035)
          ·
            refine ⟨362435452128758787529998053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241623634752505858353332035 362435452128758787529998053)
            ·
              refine ⟨67956647274142272661874635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 362435452128758787529998053 67956647274142272661874635)
              ·
                refine ⟨101934970911213408992811953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67956647274142272661874635 101934970911213408992811953)
                ·
                  refine ⟨76451228183410056744608965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101934970911213408992811953 76451228183410056744608965)
                  ·
                    refine ⟨14334605284389385639614181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76451228183410056744608965 14334605284389385639614181)
                    ·
                      refine ⟨2687738490823009807427659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14334605284389385639614181 2687738490823009807427659)
                      ·
                        rfl

theorem cell23_5234352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_5234352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234352 prefixEnd_5234352 := by exact prefixLift 5234352
  have htrace : WordTrace (prefixWord ++ tailWord_5234352) baseStart_5234352 baseEnd_5234352 := by
    simpa [prefixWord, tailWord_5234352, baseEnd_5234352] using wordTrace_append hprefix tailTrace_5234352
  have hstable : (prefixWord ++ tailWord_5234352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234352).length < 2 ^ (prefixWord ++ tailWord_5234352).sum := by decide
  have hdescent : baseEnd_5234352 < baseStart_5234352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234409 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 1, 5]
def baseStart_5234409 : Nat := 118140960795 + 5234409 * 2 ^ 59
def prefixEnd_5234409 : Nat := 4983230072969 + 3 ^ 40 * 5234409 * 2
def baseEnd_5234409 : Nat := 895922586406772028138299

theorem tailTrace_5234409 : CollatzResearch.WordTrace tailWord_5234409 prefixEnd_5234409 895922586406772028138299 := by
  unfold tailWord_5234409
  simp only [CollatzResearch.WordTrace]
  refine ⟨190914580493637633730050281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127276386995758422486700187 190914580493637633730050281)
  ·
    refine ⟨143185935370228225297537711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190914580493637633730050281 143185935370228225297537711)
    ·
      refine ⟨214778903055342337946306567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143185935370228225297537711 214778903055342337946306567)
      ·
        refine ⟨322168354583013506919459851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214778903055342337946306567 322168354583013506919459851)
        ·
          refine ⟨483252531874520260379189777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322168354583013506919459851 483252531874520260379189777)
          ·
            refine ⟨362439398905890195284392333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483252531874520260379189777 362439398905890195284392333)
            ·
              refine ⟨135914774589708823231647125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362439398905890195284392333 135914774589708823231647125)
              ·
                refine ⟨6371005058892601088983459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135914774589708823231647125 6371005058892601088983459)
                ·
                  refine ⟨9556507588338901633475189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6371005058892601088983459 9556507588338901633475189)
                  ·
                    refine ⟨895922586406772028138299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9556507588338901633475189 895922586406772028138299)
                    ·
                      rfl

theorem cell23_5234409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 5].length) (baseStart_5234409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234409 prefixEnd_5234409 := by exact prefixLift 5234409
  have htrace : WordTrace (prefixWord ++ tailWord_5234409) baseStart_5234409 baseEnd_5234409 := by
    simpa [prefixWord, tailWord_5234409, baseEnd_5234409] using wordTrace_append hprefix tailTrace_5234409
  have hstable : (prefixWord ++ tailWord_5234409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234409).length < 2 ^ (prefixWord ++ tailWord_5234409).sum := by decide
  have hdescent : baseEnd_5234409 < baseStart_5234409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234416 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 2, 3, 2]
def baseStart_5234416 : Nat := 118140960795 + 5234416 * 2 ^ 59
def prefixEnd_5234416 : Nat := 4983230072969 + 3 ^ 40 * 5234416 * 2
def baseEnd_5234416 : Nat := 2687771353584897557027365

theorem tailTrace_5234416 : CollatzResearch.WordTrace tailWord_5234416 prefixEnd_5234416 2687771353584897557027365 := by
  unfold tailWord_5234416
  simp only [CollatzResearch.WordTrace]
  refine ⟨95457417902306136962777551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127276557203074849283703401 95457417902306136962777551)
  ·
    refine ⟨143186126853459205444166327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95457417902306136962777551 143186126853459205444166327)
    ·
      refine ⟨214779190280188808166249491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143186126853459205444166327 214779190280188808166249491)
      ·
        refine ⟨322168785420283212249374237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214779190280188808166249491 322168785420283212249374237)
        ·
          refine ⟨120813294532606204593515339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322168785420283212249374237 120813294532606204593515339)
          ·
            refine ⟨181219941798909306890273009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120813294532606204593515339 181219941798909306890273009)
            ·
              refine ⟨135914956349181980167704757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181219941798909306890273009 135914956349181980167704757)
              ·
                refine ⟨12742027157735810640722321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135914956349181980167704757 12742027157735810640722321)
                ·
                  refine ⟨9556520368301857980541741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12742027157735810640722321 9556520368301857980541741)
                  ·
                    refine ⟨3583695138113196742703153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9556520368301857980541741 3583695138113196742703153)
                    ·
                      refine ⟨2687771353584897557027365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583695138113196742703153 2687771353584897557027365)
                      ·
                        rfl

theorem cell23_5234416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 3, 2].length) (baseStart_5234416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234416 prefixEnd_5234416 := by exact prefixLift 5234416
  have htrace : WordTrace (prefixWord ++ tailWord_5234416) baseStart_5234416 baseEnd_5234416 := by
    simpa [prefixWord, tailWord_5234416, baseEnd_5234416] using wordTrace_append hprefix tailTrace_5234416
  have hstable : (prefixWord ++ tailWord_5234416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234416).length < 2 ^ (prefixWord ++ tailWord_5234416).sum := by decide
  have hdescent : baseEnd_5234416 < baseStart_5234416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234423 : List Nat := [1, 1, 3, 1, 1, 1, 5, 5, 1, 1, 3]
def baseStart_5234423 : Nat := 118140960795 + 5234423 * 2 ^ 59
def prefixEnd_5234423 : Nat := 4983230072969 + 3 ^ 40 * 5234423 * 2
def baseEnd_5234423 : Nat := 2687774947949479029639833

theorem tailTrace_5234423 : CollatzResearch.WordTrace tailWord_5234423 prefixEnd_5234423 2687774947949479029639833 := by
  unfold tailWord_5234423
  simp only [CollatzResearch.WordTrace]
  refine ⟨190915091115586914121059923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127276727410391276080706615 190915091115586914121059923)
  ·
    refine ⟨286372636673380371181589885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190915091115586914121059923 286372636673380371181589885)
    ·
      refine ⟨107389738752517639193096207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286372636673380371181589885 107389738752517639193096207)
      ·
        refine ⟨161084608128776458789644311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107389738752517639193096207 161084608128776458789644311)
        ·
          refine ⟨241626912193164688184466467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161084608128776458789644311 241626912193164688184466467)
          ·
            refine ⟨362440368289747032276699701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241626912193164688184466467 362440368289747032276699701)
            ·
              refine ⟨33978784527163784275940597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 362440368289747032276699701 33978784527163784275940597)
              ·
                refine ⟨3185511049421604775869431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33978784527163784275940597 3185511049421604775869431)
                ·
                  refine ⟨4778266574132407163804147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185511049421604775869431 4778266574132407163804147)
                  ·
                    refine ⟨7167399861198610745706221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4778266574132407163804147 7167399861198610745706221)
                    ·
                      refine ⟨2687774947949479029639833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7167399861198610745706221 2687774947949479029639833)
                      ·
                        rfl

theorem cell23_5234423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 1, 1, 3].length) (baseStart_5234423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234423 prefixEnd_5234423 := by exact prefixLift 5234423
  have htrace : WordTrace (prefixWord ++ tailWord_5234423) baseStart_5234423 baseEnd_5234423 := by
    simpa [prefixWord, tailWord_5234423, baseEnd_5234423] using wordTrace_append hprefix tailTrace_5234423
  have hstable : (prefixWord ++ tailWord_5234423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234423).length < 2 ^ (prefixWord ++ tailWord_5234423).sum := by decide
  have hdescent : baseEnd_5234423 < baseStart_5234423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234429 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_5234429 : Nat := 118140960795 + 5234429 * 2 ^ 59
def prefixEnd_5234429 : Nat := 4983230072969 + 3 ^ 40 * 5234429 * 2
def baseEnd_5234429 : Nat := 2687778028833406006164805

theorem tailTrace_5234429 : CollatzResearch.WordTrace tailWord_5234429 prefixEnd_5234429 2687778028833406006164805 := by
  unfold tailWord_5234429
  simp only [CollatzResearch.WordTrace]
  refine ⟨190915309953565177145778341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127276873302376784763852227 190915309953565177145778341)
  ·
    refine ⟨35796620616293470714833439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190915309953565177145778341 35796620616293470714833439)
    ·
      refine ⟨53694930924440206072250159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35796620616293470714833439 53694930924440206072250159)
      ·
        refine ⟨80542396386660309108375239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53694930924440206072250159 80542396386660309108375239)
        ·
          refine ⟨120813594579990463662562859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80542396386660309108375239 120813594579990463662562859)
          ·
            refine ⟨181220391869985695493844289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120813594579990463662562859 181220391869985695493844289)
            ·
              refine ⟨135915293902489271620383217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181220391869985695493844289 135915293902489271620383217)
              ·
                refine ⟨101936470426866953715287413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135915293902489271620383217 101936470426866953715287413)
                ·
                  refine ⟨9556544102518776910808195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101936470426866953715287413 9556544102518776910808195)
                  ·
                    refine ⟨14334816153778165366212293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9556544102518776910808195 14334816153778165366212293)
                    ·
                      refine ⟨2687778028833406006164805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14334816153778165366212293 2687778028833406006164805)
                      ·
                        rfl

theorem cell23_5234429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_5234429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234429 prefixEnd_5234429 := by exact prefixLift 5234429
  have htrace : WordTrace (prefixWord ++ tailWord_5234429) baseStart_5234429 baseEnd_5234429 := by
    simpa [prefixWord, tailWord_5234429, baseEnd_5234429] using wordTrace_append hprefix tailTrace_5234429
  have hstable : (prefixWord ++ tailWord_5234429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234429).length < 2 ^ (prefixWord ++ tailWord_5234429).sum := by decide
  have hdescent : baseEnd_5234429 < baseStart_5234429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234430 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_5234430 : Nat := 118140960795 + 5234430 * 2 ^ 59
def prefixEnd_5234430 : Nat := 4983230072969 + 3 ^ 40 * 5234430 * 2
def baseEnd_5234430 : Nat := 298642060257117833583589

theorem tailTrace_5234430 : CollatzResearch.WordTrace tailWord_5234430 prefixEnd_5234430 298642060257117833583589 := by
  unfold tailWord_5234430
  simp only [CollatzResearch.WordTrace]
  refine ⟨23864418303320194289570593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127276897617707702877709829 23864418303320194289570593)
  ·
    refine ⟨17898313727490145717177945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23864418303320194289570593 17898313727490145717177945)
    ·
      refine ⟨13423735295617609287883459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17898313727490145717177945 13423735295617609287883459)
      ·
        refine ⟨20135602943426413931825189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13423735295617609287883459 20135602943426413931825189)
        ·
          refine ⟨3775425551892452612217223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20135602943426413931825189 3775425551892452612217223)
          ·
            refine ⟨5663138327838678918325835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775425551892452612217223 5663138327838678918325835)
            ·
              refine ⟨8494707491758018377488753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5663138327838678918325835 8494707491758018377488753)
              ·
                refine ⟨6371030618818513783116565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8494707491758018377488753 6371030618818513783116565)
                ·
                  refine ⟨298642060257117833583589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6371030618818513783116565 298642060257117833583589)
                  ·
                    rfl

theorem cell23_5234430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_5234430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234430 prefixEnd_5234430 := by exact prefixLift 5234430
  have htrace : WordTrace (prefixWord ++ tailWord_5234430) baseStart_5234430 baseEnd_5234430 := by
    simpa [prefixWord, tailWord_5234430, baseEnd_5234430] using wordTrace_append hprefix tailTrace_5234430
  have hstable : (prefixWord ++ tailWord_5234430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234430).length < 2 ^ (prefixWord ++ tailWord_5234430).sum := by decide
  have hdescent : baseEnd_5234430 < baseStart_5234430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234456 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 2, 4]
def baseStart_5234456 : Nat := 118140960795 + 5234456 * 2 ^ 59
def prefixEnd_5234456 : Nat := 4983230072969 + 3 ^ 40 * 5234456 * 2
def baseEnd_5234456 : Nat := 895930630937025800175727

theorem tailTrace_5234456 : CollatzResearch.WordTrace tailWord_5234456 prefixEnd_5234456 895930630937025800175727 := by
  unfold tailWord_5234456
  simp only [CollatzResearch.WordTrace]
  refine ⟨95458147362233680378505611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127277529816311573838007481 95458147362233680378505611)
  ·
    refine ⟨143187221043350520567758417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95458147362233680378505611 143187221043350520567758417)
    ·
      refine ⟨107390415782512890425818813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143187221043350520567758417 107390415782512890425818813)
      ·
        refine ⟨40271405918442333909682055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107390415782512890425818813 40271405918442333909682055)
        ·
          refine ⟨60407108877663500864523083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40271405918442333909682055 60407108877663500864523083)
          ·
            refine ⟨90610663316495251296784625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60407108877663500864523083 90610663316495251296784625)
            ·
              refine ⟨67957997487371438472588469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90610663316495251296784625 67957997487371438472588469)
              ·
                refine ⟨6371062264441072356805169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67957997487371438472588469 6371062264441072356805169)
                ·
                  refine ⟨4778296698330804267603877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6371062264441072356805169 4778296698330804267603877)
                  ·
                    refine ⟨895930630937025800175727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4778296698330804267603877 895930630937025800175727)
                    ·
                      rfl

theorem cell23_5234456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_5234456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234456 prefixEnd_5234456 := by exact prefixLift 5234456
  have htrace : WordTrace (prefixWord ++ tailWord_5234456) baseStart_5234456 baseEnd_5234456 := by
    simpa [prefixWord, tailWord_5234456, baseEnd_5234456] using wordTrace_append hprefix tailTrace_5234456
  have hstable : (prefixWord ++ tailWord_5234456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234456).length < 2 ^ (prefixWord ++ tailWord_5234456).sum := by decide
  have hdescent : baseEnd_5234456 < baseStart_5234456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234463 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 3, 2, 2]
def baseStart_5234463 : Nat := 118140960795 + 5234463 * 2 ^ 59
def prefixEnd_5234463 : Nat := 4983230072969 + 3 ^ 40 * 5234463 * 2
def baseEnd_5234463 : Nat := 2687795487175658873139649

theorem tailTrace_5234463 : CollatzResearch.WordTrace tailWord_5234463 prefixEnd_5234463 2687795487175658873139649 := by
  unfold tailWord_5234463
  simp only [CollatzResearch.WordTrace]
  refine ⟨190916550035442000952516043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127277700023628000635010695 190916550035442000952516043)
  ·
    refine ⟨286374825053163001428774065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190916550035442000952516043 286374825053163001428774065)
    ·
      refine ⟨214781118789872251071580549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286374825053163001428774065 214781118789872251071580549)
      ·
        refine ⟨40271459773101047075921353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214781118789872251071580549 40271459773101047075921353)
        ·
          refine ⟨30203594829825785306941015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40271459773101047075921353 30203594829825785306941015)
          ·
            refine ⟨45305392244738677960411523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30203594829825785306941015 45305392244738677960411523)
            ·
              refine ⟨67958088367108016940617285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45305392244738677960411523 67958088367108016940617285)
              ·
                refine ⟨12742141568832753176365741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67958088367108016940617285 12742141568832753176365741)
                ·
                  refine ⟨4778303088312282441137153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12742141568832753176365741 4778303088312282441137153)
                  ·
                    refine ⟨3583727316234211830852865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4778303088312282441137153 3583727316234211830852865)
                    ·
                      refine ⟨2687795487175658873139649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583727316234211830852865 2687795487175658873139649)
                      ·
                        rfl

theorem cell23_5234463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_5234463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234463 prefixEnd_5234463 := by exact prefixLift 5234463
  have htrace : WordTrace (prefixWord ++ tailWord_5234463) baseStart_5234463 baseEnd_5234463 := by
    simpa [prefixWord, tailWord_5234463, baseEnd_5234463] using wordTrace_append hprefix tailTrace_5234463
  have hstable : (prefixWord ++ tailWord_5234463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234463).length < 2 ^ (prefixWord ++ tailWord_5234463).sum := by decide
  have hdescent : baseEnd_5234463 < baseStart_5234463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234469 : List Nat := [1, 3, 1, 2, 3, 3, 1, 9]
def baseStart_5234469 : Nat := 118140960795 + 5234469 * 2 ^ 59
def prefixEnd_5234469 : Nat := 4983230072969 + 3 ^ 40 * 5234469 * 2
def baseEnd_5234469 : Nat := 99548095113317994432023

theorem tailTrace_5234469 : CollatzResearch.WordTrace tailWord_5234469 prefixEnd_5234469 99548095113317994432023 := by
  unfold tailWord_5234469
  simp only [CollatzResearch.WordTrace]
  refine ⟨190916768873420263977234461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127277845915613509318156307 190916768873420263977234461)
  ·
    refine ⟨71593788327532598991462923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190916768873420263977234461 71593788327532598991462923)
    ·
      refine ⟨107390682491298898487194385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71593788327532598991462923 107390682491298898487194385)
      ·
        refine ⟨80543011868474173865395789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107390682491298898487194385 80543011868474173865395789)
        ·
          refine ⟨30203629450677815199523421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80543011868474173865395789 30203629450677815199523421)
          ·
            refine ⟨11326361044004180699821283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30203629450677815199523421 11326361044004180699821283)
            ·
              refine ⟨16989541566006271049731925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11326361044004180699821283 16989541566006271049731925)
              ·
                refine ⟨99548095113317994432023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16989541566006271049731925 99548095113317994432023)
                ·
                  rfl

theorem cell23_5234469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 9].length) (baseStart_5234469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234469 prefixEnd_5234469 := by exact prefixLift 5234469
  have htrace : WordTrace (prefixWord ++ tailWord_5234469) baseStart_5234469 baseEnd_5234469 := by
    simpa [prefixWord, tailWord_5234469, baseEnd_5234469] using wordTrace_append hprefix tailTrace_5234469
  have hstable : (prefixWord ++ tailWord_5234469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234469).length < 2 ^ (prefixWord ++ tailWord_5234469).sum := by decide
  have hdescent : baseEnd_5234469 < baseStart_5234469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234486 : List Nat := [5, 1, 2, 2, 1, 1, 11]
def baseStart_5234486 : Nat := 118140960795 + 5234486 * 2 ^ 59
def prefixEnd_5234486 : Nat := 4983230072969 + 3 ^ 40 * 5234486 * 2
def baseEnd_5234486 : Nat := 33182806138650768927803

theorem tailTrace_5234486 : CollatzResearch.WordTrace tailWord_5234486 prefixEnd_5234486 33182806138650768927803 := by
  unfold tailWord_5234486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11932336807147417242537707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127278259276239117253735541 11932336807147417242537707)
  ·
    refine ⟨17898505210721125863806561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11932336807147417242537707 17898505210721125863806561)
    ·
      refine ⟨13423878908040844397854921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17898505210721125863806561 13423878908040844397854921)
      ·
        refine ⟨10067909181030633298391191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13423878908040844397854921 10067909181030633298391191)
        ·
          refine ⟨15101863771545949947586787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10067909181030633298391191 15101863771545949947586787)
          ·
            refine ⟨22652795657318924921380181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15101863771545949947586787 22652795657318924921380181)
            ·
              refine ⟨33182806138650768927803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22652795657318924921380181 33182806138650768927803)
              ·
                rfl

theorem cell23_5234486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 11].length) (baseStart_5234486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234486 prefixEnd_5234486 := by exact prefixLift 5234486
  have htrace : WordTrace (prefixWord ++ tailWord_5234486) baseStart_5234486 baseEnd_5234486 := by
    simpa [prefixWord, tailWord_5234486, baseEnd_5234486] using wordTrace_append hprefix tailTrace_5234486
  have hstable : (prefixWord ++ tailWord_5234486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234486).length < 2 ^ (prefixWord ++ tailWord_5234486).sum := by decide
  have hdescent : baseEnd_5234486 < baseStart_5234486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234559 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 7]
def baseStart_5234559 : Nat := 118140960795 + 5234559 * 2 ^ 59
def prefixEnd_5234559 : Nat := 4983230072969 + 3 ^ 40 * 5234559 * 2
def baseEnd_5234559 : Nat := 298649420146498944171023

theorem tailTrace_5234559 : CollatzResearch.WordTrace tailWord_5234559 prefixEnd_5234559 298649420146498944171023 := by
  unfold tailWord_5234559
  simp only [CollatzResearch.WordTrace]
  refine ⟨190920051443094209348010731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127280034295396139565340487 190920051443094209348010731)
  ·
    refine ⟨286380077164641314022016097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190920051443094209348010731 286380077164641314022016097)
    ·
      refine ⟨214785057873480985516512073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286380077164641314022016097 214785057873480985516512073)
      ·
        refine ⟨161088793405110739137384055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214785057873480985516512073 161088793405110739137384055)
        ·
          refine ⟨241633190107666108706076083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161088793405110739137384055 241633190107666108706076083)
          ·
            refine ⟨362449785161499163059114125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241633190107666108706076083 362449785161499163059114125)
            ·
              refine ⟨135918669435562186147167797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362449785161499163059114125 135918669435562186147167797)
              ·
                refine ⟨12742375259583954951296981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135918669435562186147167797 12742375259583954951296981)
                ·
                  refine ⟨298649420146498944171023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12742375259583954951296981 298649420146498944171023)
                  ·
                    rfl

theorem cell23_5234559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 7].length) (baseStart_5234559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234559 prefixEnd_5234559 := by exact prefixLift 5234559
  have htrace : WordTrace (prefixWord ++ tailWord_5234559) baseStart_5234559 baseEnd_5234559 := by
    simpa [prefixWord, tailWord_5234559, baseEnd_5234559] using wordTrace_append hprefix tailTrace_5234559
  have hstable : (prefixWord ++ tailWord_5234559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234559).length < 2 ^ (prefixWord ++ tailWord_5234559).sum := by decide
  have hdescent : baseEnd_5234559 < baseStart_5234559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234619 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 2, 8]
def baseStart_5234619 : Nat := 118140960795 + 5234619 * 2 ^ 59
def prefixEnd_5234619 : Nat := 4983230072969 + 3 ^ 40 * 5234619 * 2
def baseEnd_5234619 : Nat := 895958530052586754262977

theorem tailTrace_5234619 : CollatzResearch.WordTrace tailWord_5234619 prefixEnd_5234619 895958530052586754262977 := by
  unfold tailWord_5234619
  simp only [CollatzResearch.WordTrace]
  refine ⟨190922239822876839595194911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127281493215251226396796607 190922239822876839595194911)
  ·
    refine ⟨286383359734315259392792367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190922239822876839595194911 286383359734315259392792367)
    ·
      refine ⟨429575039601472889089188551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286383359734315259392792367 429575039601472889089188551)
      ·
        refine ⟨644362559402209333633782827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429575039601472889089188551 644362559402209333633782827)
        ·
          refine ⟨966543839103314000450674241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644362559402209333633782827 966543839103314000450674241)
          ·
            refine ⟨724907879327485500338005681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966543839103314000450674241 724907879327485500338005681)
            ·
              refine ⟨543680909495614125253504261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724907879327485500338005681 543680909495614125253504261)
              ·
                refine ⟨101940170530427648485032049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 543680909495614125253504261 101940170530427648485032049)
                ·
                  refine ⟨76455127897820736363774037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101940170530427648485032049 76455127897820736363774037)
                  ·
                    refine ⟨895958530052586754262977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76455127897820736363774037 895958530052586754262977)
                    ·
                      rfl

theorem cell23_5234619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 8].length) (baseStart_5234619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234619 prefixEnd_5234619 := by exact prefixLift 5234619
  have htrace : WordTrace (prefixWord ++ tailWord_5234619) baseStart_5234619 baseEnd_5234619 := by
    simpa [prefixWord, tailWord_5234619, baseEnd_5234619] using wordTrace_append hprefix tailTrace_5234619
  have hstable : (prefixWord ++ tailWord_5234619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234619).length < 2 ^ (prefixWord ++ tailWord_5234619).sum := by decide
  have hdescent : baseEnd_5234619 < baseStart_5234619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234666 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 8]
def baseStart_5234666 : Nat := 118140960795 + 5234666 * 2 ^ 59
def prefixEnd_5234666 : Nat := 4983230072969 + 3 ^ 40 * 5234666 * 2
def baseEnd_5234666 : Nat := 298655524860946842100135

theorem tailTrace_5234666 : CollatzResearch.WordTrace tailWord_5234666 prefixEnd_5234666 298655524860946842100135 := by
  unfold tailWord_5234666
  simp only [CollatzResearch.WordTrace]
  refine ⟨47730988513426641655538963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127282636035804377748103901 47730988513426641655538963)
  ·
    refine ⟨71596482770139962483308445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47730988513426641655538963 71596482770139962483308445)
    ·
      refine ⟨26848681038802485931240667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71596482770139962483308445 26848681038802485931240667)
      ·
        refine ⟨40273021558203728896861001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26848681038802485931240667 40273021558203728896861001)
        ·
          refine ⟨30204766168652796672645751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40273021558203728896861001 30204766168652796672645751)
          ·
            refine ⟨45307149252979195008968627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30204766168652796672645751 45307149252979195008968627)
            ·
              refine ⟨67960723879468792513452941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45307149252979195008968627 67960723879468792513452941)
              ·
                refine ⟨25485271454800797192544853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67960723879468792513452941 25485271454800797192544853)
                ·
                  refine ⟨298655524860946842100135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25485271454800797192544853 298655524860946842100135)
                  ·
                    rfl

theorem cell23_5234666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_5234666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234666 prefixEnd_5234666 := by exact prefixLift 5234666
  have htrace : WordTrace (prefixWord ++ tailWord_5234666) baseStart_5234666 baseEnd_5234666 := by
    simpa [prefixWord, tailWord_5234666, baseEnd_5234666] using wordTrace_append hprefix tailTrace_5234666
  have hstable : (prefixWord ++ tailWord_5234666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234666).length < 2 ^ (prefixWord ++ tailWord_5234666).sum := by decide
  have hdescent : baseEnd_5234666 < baseStart_5234666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234670 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_5234670 : Nat := 118140960795 + 5234670 * 2 ^ 59
def prefixEnd_5234670 : Nat := 4983230072969 + 3 ^ 40 * 5234670 * 2
def baseEnd_5234670 : Nat := 895967259223713187750399

theorem tailTrace_5234670 : CollatzResearch.WordTrace tailWord_5234670 prefixEnd_5234670 895967259223713187750399 := by
  unfold tailWord_5234670
  simp only [CollatzResearch.WordTrace]
  refine ⟨23865512493211509413162683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127282733297128050203534309 23865512493211509413162683)
  ·
    refine ⟨35798268739817264119744025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23865512493211509413162683 35798268739817264119744025)
    ·
      refine ⟨26848701554862948089808019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35798268739817264119744025 26848701554862948089808019)
      ·
        refine ⟨40273052332294422134712029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26848701554862948089808019 40273052332294422134712029)
        ·
          refine ⟨15102394624610408300517011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40273052332294422134712029 15102394624610408300517011)
          ·
            refine ⟨22653591936915612450775517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15102394624610408300517011 22653591936915612450775517)
            ·
              refine ⟨8495096976343354669040819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22653591936915612450775517 8495096976343354669040819)
              ·
                refine ⟨12742645464515032003561229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8495096976343354669040819 12742645464515032003561229)
                ·
                  refine ⟨4778492049193137001335461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12742645464515032003561229 4778492049193137001335461)
                  ·
                    refine ⟨895967259223713187750399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4778492049193137001335461 895967259223713187750399)
                    ·
                      rfl

theorem cell23_5234670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_5234670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234670 prefixEnd_5234670 := by exact prefixLift 5234670
  have htrace : WordTrace (prefixWord ++ tailWord_5234670) baseStart_5234670 baseEnd_5234670 := by
    simpa [prefixWord, tailWord_5234670, baseEnd_5234670] using wordTrace_append hprefix tailTrace_5234670
  have hstable : (prefixWord ++ tailWord_5234670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234670).length < 2 ^ (prefixWord ++ tailWord_5234670).sum := by decide
  have hdescent : baseEnd_5234670 < baseStart_5234670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234683 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 6]
def baseStart_5234683 : Nat := 118140960795 + 5234683 * 2 ^ 59
def prefixEnd_5234683 : Nat := 4983230072969 + 3 ^ 40 * 5234683 * 2
def baseEnd_5234683 : Nat := 298656494768849779154293

theorem tailTrace_5234683 : CollatzResearch.WordTrace tailWord_5234683 prefixEnd_5234683 298656494768849779154293 := by
  unfold tailWord_5234683
  simp only [CollatzResearch.WordTrace]
  refine ⟨190924574094644978525524703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127283049396429985683683135 190924574094644978525524703)
  ·
    refine ⟨286386861141967467788287055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190924574094644978525524703 286386861141967467788287055)
    ·
      refine ⟨429580291712951201682430583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286386861141967467788287055 429580291712951201682430583)
      ·
        refine ⟨644370437569426802523645875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429580291712951201682430583 644370437569426802523645875)
        ·
          refine ⟨966555656354140203785468813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644370437569426802523645875 966555656354140203785468813)
          ·
            refine ⟨362458371132802576419550805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 966555656354140203785468813 362458371132802576419550805)
            ·
              refine ⟨4247559036712530192416611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 362458371132802576419550805 4247559036712530192416611)
              ·
                refine ⟨6371338555068795288624917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4247559036712530192416611 6371338555068795288624917)
                ·
                  refine ⟨298656494768849779154293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6371338555068795288624917 298656494768849779154293)
                  ·
                    rfl

theorem cell23_5234683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 6].length) (baseStart_5234683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234683 prefixEnd_5234683 := by exact prefixLift 5234683
  have htrace : WordTrace (prefixWord ++ tailWord_5234683) baseStart_5234683 baseEnd_5234683 := by
    simpa [prefixWord, tailWord_5234683, baseEnd_5234683] using wordTrace_append hprefix tailTrace_5234683
  have hstable : (prefixWord ++ tailWord_5234683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234683).length < 2 ^ (prefixWord ++ tailWord_5234683).sum := by decide
  have hdescent : baseEnd_5234683 < baseStart_5234683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234721 : List Nat := [1, 2, 3, 2, 5, 1, 2, 2, 1, 4]
def baseStart_5234721 : Nat := 118140960795 + 5234721 * 2 ^ 59
def prefixEnd_5234721 : Nat := 4983230072969 + 3 ^ 40 * 5234721 * 2
def baseEnd_5234721 : Nat := 895975988394839621237821

theorem tailTrace_5234721 : CollatzResearch.WordTrace tailWord_5234721 prefixEnd_5234721 895975988394839621237821 := by
  unfold tailWord_5234721
  simp only [CollatzResearch.WordTrace]
  refine ⟨190925960068507311015408017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127283973379004874010272011 190925960068507311015408017)
  ·
    refine ⟨143194470051380483261556013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190925960068507311015408017 143194470051380483261556013)
    ·
      refine ⟨53697926269267681223083505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143194470051380483261556013 53697926269267681223083505)
      ·
        refine ⟨40273444701950760917312629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53697926269267681223083505 40273444701950760917312629)
        ·
          refine ⟨3775635440807883835998059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40273444701950760917312629 3775635440807883835998059)
          ·
            refine ⟨5663453161211825753997089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775635440807883835998059 5663453161211825753997089)
            ·
              refine ⟨4247589870908869315497817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5663453161211825753997089 4247589870908869315497817)
              ·
                refine ⟨3185692403181651986623363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247589870908869315497817 3185692403181651986623363)
                ·
                  refine ⟨4778538604772477979935045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185692403181651986623363 4778538604772477979935045)
                  ·
                    refine ⟨895975988394839621237821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4778538604772477979935045 895975988394839621237821)
                    ·
                      rfl

theorem cell23_5234721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_5234721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234721 prefixEnd_5234721 := by exact prefixLift 5234721
  have htrace : WordTrace (prefixWord ++ tailWord_5234721) baseStart_5234721 baseEnd_5234721 := by
    simpa [prefixWord, tailWord_5234721, baseEnd_5234721] using wordTrace_append hprefix tailTrace_5234721
  have hstable : (prefixWord ++ tailWord_5234721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234721).length < 2 ^ (prefixWord ++ tailWord_5234721).sum := by decide
  have hdescent : baseEnd_5234721 < baseStart_5234721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234784 : List Nat := [2, 1, 1, 3, 2, 3, 2, 4, 1, 2, 2]
def baseStart_5234784 : Nat := 118140960795 + 5234784 * 2 ^ 59
def prefixEnd_5234784 : Nat := 4983230072969 + 3 ^ 40 * 5234784 * 2
def baseEnd_5234784 : Nat := 2687960314465752117225673

theorem tailTrace_5234784 : CollatzResearch.WordTrace tailWord_5234784 prefixEnd_5234784 2687960314465752117225673 := by
  unfold tailWord_5234784
  simp only [CollatzResearch.WordTrace]
  refine ⟨95464128933639536387475703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127285505244852715183300937 95464128933639536387475703)
  ·
    refine ⟨143196193400459304581213555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95464128933639536387475703 143196193400459304581213555)
    ·
      refine ⟨214794290100688956871820333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143196193400459304581213555 214794290100688956871820333)
      ·
        refine ⟨80547858787758358826932625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214794290100688956871820333 80547858787758358826932625)
        ·
          refine ⟨60410894090818769120199469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80547858787758358826932625 60410894090818769120199469)
          ·
            refine ⟨22654085284057038420074801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60410894090818769120199469 22654085284057038420074801)
            ·
              refine ⟨16990563963042778815056101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22654085284057038420074801 16990563963042778815056101)
              ·
                refine ⟨3185730743070521027823019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16990563963042778815056101 3185730743070521027823019)
                ·
                  refine ⟨4778596114605781541734529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185730743070521027823019 4778596114605781541734529)
                  ·
                    refine ⟨3583947085954336156300897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4778596114605781541734529 3583947085954336156300897)
                    ·
                      refine ⟨2687960314465752117225673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583947085954336156300897 2687960314465752117225673)
                      ·
                        rfl

theorem cell23_5234784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_5234784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234784 prefixEnd_5234784 := by exact prefixLift 5234784
  have htrace : WordTrace (prefixWord ++ tailWord_5234784) baseStart_5234784 baseEnd_5234784 := by
    simpa [prefixWord, tailWord_5234784, baseEnd_5234784] using wordTrace_append hprefix tailTrace_5234784
  have hstable : (prefixWord ++ tailWord_5234784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234784).length < 2 ^ (prefixWord ++ tailWord_5234784).sum := by decide
  have hdescent : baseEnd_5234784 < baseStart_5234784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234794 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_5234794 : Nat := 118140960795 + 5234794 * 2 ^ 59
def prefixEnd_5234794 : Nat := 4983230072969 + 3 ^ 40 * 5234794 * 2
def baseEnd_5234794 : Nat := 895988483090765692700209

theorem tailTrace_5234794 : CollatzResearch.WordTrace tailWord_5234794 prefixEnd_5234794 895988483090765692700209 := by
  unfold tailWord_5234794
  simp only [CollatzResearch.WordTrace]
  refine ⟨47732155649310711120703859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127285748398161896321876957 47732155649310711120703859)
  ·
    refine ⟨71598233473966066681055789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47732155649310711120703859 71598233473966066681055789)
    ·
      refine ⟨26849337552737275005395921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71598233473966066681055789 26849337552737275005395921)
      ·
        refine ⟨20137003164552956254046941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26849337552737275005395921 20137003164552956254046941)
        ·
          refine ⟨7551376186707358595267603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20137003164552956254046941 7551376186707358595267603)
          ·
            refine ⟨11327064280061037892901405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7551376186707358595267603 11327064280061037892901405)
            ·
              refine ⟨4247649105022889209838027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11327064280061037892901405 4247649105022889209838027)
              ·
                refine ⟨6371473657534333814757041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4247649105022889209838027 6371473657534333814757041)
                ·
                  refine ⟨4778605243150750361067781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6371473657534333814757041 4778605243150750361067781)
                  ·
                    refine ⟨895988483090765692700209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4778605243150750361067781 895988483090765692700209)
                    ·
                      rfl

theorem cell23_5234794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_5234794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234794 prefixEnd_5234794 := by exact prefixLift 5234794
  have htrace : WordTrace (prefixWord ++ tailWord_5234794) baseStart_5234794 baseEnd_5234794 := by
    simpa [prefixWord, tailWord_5234794, baseEnd_5234794] using wordTrace_append hprefix tailTrace_5234794
  have hstable : (prefixWord ++ tailWord_5234794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234794).length < 2 ^ (prefixWord ++ tailWord_5234794).sum := by decide
  have hdescent : baseEnd_5234794 < baseStart_5234794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234800 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 3]
def baseStart_5234800 : Nat := 118140960795 + 5234800 * 2 ^ 59
def prefixEnd_5234800 : Nat := 4983230072969 + 3 ^ 40 * 5234800 * 2
def baseEnd_5234800 : Nat := 2687968530156224054625599

theorem tailTrace_5234800 : CollatzResearch.WordTrace tailWord_5234800 prefixEnd_5234800 2687968530156224054625599 := by
  unfold tailWord_5234800
  simp only [CollatzResearch.WordTrace]
  refine ⟨95464420717610553753766927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127285894290147405005022569 95464420717610553753766927)
  ·
    refine ⟨143196631076415830630650391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95464420717610553753766927 143196631076415830630650391)
    ·
      refine ⟨214794946614623745945975587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143196631076415830630650391 214794946614623745945975587)
      ·
        refine ⟨322192419921935618918963381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214794946614623745945975587 322192419921935618918963381)
        ·
          refine ⟨30205539367681464273652817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 322192419921935618918963381 30205539367681464273652817)
          ·
            refine ⟨22654154525761098205239613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30205539367681464273652817 22654154525761098205239613)
            ·
              refine ⟨8495307947160411826964855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22654154525761098205239613 8495307947160411826964855)
              ·
                refine ⟨12742961920740617740447283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8495307947160411826964855 12742961920740617740447283)
                ·
                  refine ⟨19114442881110926610670925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12742961920740617740447283 19114442881110926610670925)
                  ·
                    refine ⟨7167916080416597479001597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19114442881110926610670925 7167916080416597479001597)
                    ·
                      refine ⟨2687968530156224054625599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7167916080416597479001597 2687968530156224054625599)
                      ·
                        rfl

theorem cell23_5234800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_5234800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234800 prefixEnd_5234800 := by exact prefixLift 5234800
  have htrace : WordTrace (prefixWord ++ tailWord_5234800) baseStart_5234800 baseEnd_5234800 := by
    simpa [prefixWord, tailWord_5234800, baseEnd_5234800] using wordTrace_append hprefix tailTrace_5234800
  have hstable : (prefixWord ++ tailWord_5234800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234800).length < 2 ^ (prefixWord ++ tailWord_5234800).sum := by decide
  have hdescent : baseEnd_5234800 < baseStart_5234800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234813 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_5234813 : Nat := 118140960795 + 5234813 * 2 ^ 59
def prefixEnd_5234813 : Nat := 4983230072969 + 3 ^ 40 * 5234813 * 2
def baseEnd_5234813 : Nat := 2687975205404732503763039

theorem tailTrace_5234813 : CollatzResearch.WordTrace tailWord_5234813 prefixEnd_5234813 2687975205404732503763039 := by
  unfold tailWord_5234813
  simp only [CollatzResearch.WordTrace]
  refine ⟨190929315584174010727757093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127286210389449340485171395 190929315584174010727757093)
  ·
    refine ⟨35799246672032627011454455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190929315584174010727757093 35799246672032627011454455)
    ·
      refine ⟨53698870008048940517181683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35799246672032627011454455 53698870008048940517181683)
      ·
        refine ⟨80548305012073410775772525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53698870008048940517181683 80548305012073410775772525)
        ·
          refine ⟨30205614379527529040914697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80548305012073410775772525 30205614379527529040914697)
          ·
            refine ⟨22654210784645646780686023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30205614379527529040914697 22654210784645646780686023)
            ·
              refine ⟨33981316176968470171029035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22654210784645646780686023 33981316176968470171029035)
              ·
                refine ⟨50971974265452705256543553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33981316176968470171029035 50971974265452705256543553)
                ·
                  refine ⟨38228980699089528942407665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50971974265452705256543553 38228980699089528942407665)
                  ·
                    refine ⟨28671735524317146706805749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38228980699089528942407665 28671735524317146706805749)
                    ·
                      refine ⟨2687975205404732503763039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28671735524317146706805749 2687975205404732503763039)
                      ·
                        rfl

theorem cell23_5234813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_5234813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234813 prefixEnd_5234813 := by exact prefixLift 5234813
  have htrace : WordTrace (prefixWord ++ tailWord_5234813) baseStart_5234813 baseEnd_5234813 := by
    simpa [prefixWord, tailWord_5234813, baseEnd_5234813] using wordTrace_append hprefix tailTrace_5234813
  have hstable : (prefixWord ++ tailWord_5234813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234813).length < 2 ^ (prefixWord ++ tailWord_5234813).sum := by decide
  have hdescent : baseEnd_5234813 < baseStart_5234813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234853 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_5234853 : Nat := 118140960795 + 5234853 * 2 ^ 59
def prefixEnd_5234853 : Nat := 4983230072969 + 3 ^ 40 * 5234853 * 2
def baseEnd_5234853 : Nat := 2687995744630912347262855

theorem tailTrace_5234853 : CollatzResearch.WordTrace tailWord_5234853 prefixEnd_5234853 2687995744630912347262855 := by
  unfold tailWord_5234853
  simp only [CollatzResearch.WordTrace]
  refine ⟨190930774504029097559213213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127287183002686065039475475 190930774504029097559213213)
  ·
    refine ⟨71599040439010911584704955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190930774504029097559213213 71599040439010911584704955)
    ·
      refine ⟨107398560658516367377057433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71599040439010911584704955 107398560658516367377057433)
      ·
        refine ⟨80548920493887275532793075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107398560658516367377057433 80548920493887275532793075)
        ·
          refine ⟨120823380740830913299189613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80548920493887275532793075 120823380740830913299189613)
          ·
            refine ⟨45308767777811592487196105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120823380740830913299189613 45308767777811592487196105)
            ·
              refine ⟨33981575833358694365397079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45308767777811592487196105 33981575833358694365397079)
              ·
                refine ⟨50972363750038041548095619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33981575833358694365397079 50972363750038041548095619)
                ·
                  refine ⟨76458545625057062322143429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50972363750038041548095619 76458545625057062322143429)
                  ·
                    refine ⟨14335977304698199185401893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76458545625057062322143429 14335977304698199185401893)
                    ·
                      refine ⟨2687995744630912347262855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14335977304698199185401893 2687995744630912347262855)
                      ·
                        rfl

theorem cell23_5234853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_5234853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234853 prefixEnd_5234853 := by exact prefixLift 5234853
  have htrace : WordTrace (prefixWord ++ tailWord_5234853) baseStart_5234853 baseEnd_5234853 := by
    simpa [prefixWord, tailWord_5234853, baseEnd_5234853] using wordTrace_append hprefix tailTrace_5234853
  have hstable : (prefixWord ++ tailWord_5234853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234853).length < 2 ^ (prefixWord ++ tailWord_5234853).sum := by decide
  have hdescent : baseEnd_5234853 < baseStart_5234853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234861 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_5234861 : Nat := 118140960795 + 5234861 * 2 ^ 59
def prefixEnd_5234861 : Nat := 4983230072969 + 3 ^ 40 * 5234861 * 2
def baseEnd_5234861 : Nat := 2687999852476148315962819

theorem tailTrace_5234861 : CollatzResearch.WordTrace tailWord_5234861 prefixEnd_5234861 2687999852476148315962819 := by
  unfold tailWord_5234861
  simp only [CollatzResearch.WordTrace]
  refine ⟨190931066288000114925504437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127287377525333409950336291 190931066288000114925504437)
  ·
    refine ⟨17899787464500010774266041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190931066288000114925504437 17899787464500010774266041)
    ·
      refine ⟨13424840598375008080699531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17899787464500010774266041 13424840598375008080699531)
      ·
        refine ⟨20137260897562512121049297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13424840598375008080699531 20137260897562512121049297)
        ·
          refine ⟨15102945673171884090786973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20137260897562512121049297 15102945673171884090786973)
          ·
            refine ⟨5663604627439456534045115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15102945673171884090786973 5663604627439456534045115)
            ·
              refine ⟨8495406941159184801067673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5663604627439456534045115 8495406941159184801067673)
              ·
                refine ⟨6371555205869388600800755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8495406941159184801067673 6371555205869388600800755)
                ·
                  refine ⟨9557332808804082901201133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6371555205869388600800755 9557332808804082901201133)
                  ·
                    refine ⟨3583999803301531087950425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9557332808804082901201133 3583999803301531087950425)
                    ·
                      refine ⟨2687999852476148315962819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3583999803301531087950425 2687999852476148315962819)
                      ·
                        rfl

theorem cell23_5234861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_5234861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234861 prefixEnd_5234861 := by exact prefixLift 5234861
  have htrace : WordTrace (prefixWord ++ tailWord_5234861) baseStart_5234861 baseEnd_5234861 := by
    simpa [prefixWord, tailWord_5234861, baseEnd_5234861] using wordTrace_append hprefix tailTrace_5234861
  have hstable : (prefixWord ++ tailWord_5234861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234861).length < 2 ^ (prefixWord ++ tailWord_5234861).sum := by decide
  have hdescent : baseEnd_5234861 < baseStart_5234861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234890 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_5234890 : Nat := 118140960795 + 5234890 * 2 ^ 59
def prefixEnd_5234890 : Nat := 4983230072969 + 3 ^ 40 * 5234890 * 2
def baseEnd_5234890 : Nat := 2688014743415128702500185

theorem tailTrace_5234890 : CollatzResearch.WordTrace tailWord_5234890 prefixEnd_5234890 2688014743415128702500185 := by
  unfold tailWord_5234890
  simp only [CollatzResearch.WordTrace]
  refine ⟨47733031001223763219577531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127288082669930035252206749 47733031001223763219577531)
  ·
    refine ⟨71599546501835644829366297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47733031001223763219577531 71599546501835644829366297)
    ·
      refine ⟨53699659876376733622024723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71599546501835644829366297 53699659876376733622024723)
      ·
        refine ⟨80549489814565100433037085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53699659876376733622024723 80549489814565100433037085)
        ·
          refine ⟨30206058680461912662388907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80549489814565100433037085 30206058680461912662388907)
          ·
            refine ⟨45309088020692868993583361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30206058680461912662388907 45309088020692868993583361)
            ·
              refine ⟨33981816015519651745187521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45309088020692868993583361 33981816015519651745187521)
              ·
                refine ⟨25486362011639738808890641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33981816015519651745187521 25486362011639738808890641)
                ·
                  refine ⟨19114771508729804106667981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25486362011639738808890641 19114771508729804106667981)
                  ·
                    refine ⟨7168039315773676540000493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19114771508729804106667981 7168039315773676540000493)
                    ·
                      refine ⟨2688014743415128702500185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7168039315773676540000493 2688014743415128702500185)
                      ·
                        rfl

theorem cell23_5234890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_5234890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234890 prefixEnd_5234890 := by exact prefixLift 5234890
  have htrace : WordTrace (prefixWord ++ tailWord_5234890) baseStart_5234890 baseEnd_5234890 := by
    simpa [prefixWord, tailWord_5234890, baseEnd_5234890] using wordTrace_append hprefix tailTrace_5234890
  have hstable : (prefixWord ++ tailWord_5234890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234890).length < 2 ^ (prefixWord ++ tailWord_5234890).sum := by decide
  have hdescent : baseEnd_5234890 < baseStart_5234890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234897 : List Nat := [1, 2, 2, 1, 2, 2, 6, 2, 5]
def baseStart_5234897 : Nat := 118140960795 + 5234897 * 2 ^ 59
def prefixEnd_5234897 : Nat := 4983230072969 + 3 ^ 40 * 5234897 * 2
def baseEnd_5234897 : Nat := 298668704197745575012517

theorem tailTrace_5234897 : CollatzResearch.WordTrace tailWord_5234897 prefixEnd_5234897 298668704197745575012517 := by
  unfold tailWord_5234897
  simp only [CollatzResearch.WordTrace]
  refine ⟨190932379315869693073814945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127288252877246462049209963 190932379315869693073814945)
  ·
    refine ⟨143199284486902269805361209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190932379315869693073814945 143199284486902269805361209)
    ·
      refine ⟨107399463365176702354020907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143199284486902269805361209 107399463365176702354020907)
      ·
        refine ⟨161099195047765053531031361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107399463365176702354020907 161099195047765053531031361)
        ·
          refine ⟨120824396285823790148273521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161099195047765053531031361 120824396285823790148273521)
          ·
            refine ⟨90618297214367842611205141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120824396285823790148273521 90618297214367842611205141)
            ·
              refine ⟨4247732681923492622400241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90618297214367842611205141 4247732681923492622400241)
              ·
                refine ⟨3185799511442619466800181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4247732681923492622400241 3185799511442619466800181)
                ·
                  refine ⟨298668704197745575012517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3185799511442619466800181 298668704197745575012517)
                  ·
                    rfl

theorem cell23_5234897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 5].length) (baseStart_5234897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234897 prefixEnd_5234897 := by exact prefixLift 5234897
  have htrace : WordTrace (prefixWord ++ tailWord_5234897) baseStart_5234897 baseEnd_5234897 := by
    simpa [prefixWord, tailWord_5234897, baseEnd_5234897] using wordTrace_append hprefix tailTrace_5234897
  have hstable : (prefixWord ++ tailWord_5234897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234897).length < 2 ^ (prefixWord ++ tailWord_5234897).sum := by decide
  have hdescent : baseEnd_5234897 < baseStart_5234897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234927 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 2, 5]
def baseStart_5234927 : Nat := 118140960795 + 5234927 * 2 ^ 59
def prefixEnd_5234927 : Nat := 4983230072969 + 3 ^ 40 * 5234927 * 2
def baseEnd_5234927 : Nat := 896011247399781685912505

theorem tailTrace_5234927 : CollatzResearch.WordTrace tailWord_5234927 prefixEnd_5234927 896011247399781685912505 := by
  unfold tailWord_5234927
  simp only [CollatzResearch.WordTrace]
  refine ⟨190933473505761008197407035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127288982337174005464938023 190933473505761008197407035)
  ·
    refine ⟨286400210258641512296110553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190933473505761008197407035 286400210258641512296110553)
    ·
      refine ⟨214800157693981134222082915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286400210258641512296110553 214800157693981134222082915)
      ·
        refine ⟨322200236540971701333124373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214800157693981134222082915 322200236540971701333124373)
        ·
          refine ⟨15103136087858048499990205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 322200236540971701333124373 15103136087858048499990205)
          ·
            refine ⟨5663676032946768187496327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15103136087858048499990205 5663676032946768187496327)
            ·
              refine ⟨8495514049420152281244491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5663676032946768187496327 8495514049420152281244491)
              ·
                refine ⟨12743271074130228421866737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8495514049420152281244491 12743271074130228421866737)
                ·
                  refine ⟨9557453305597671316400053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12743271074130228421866737 9557453305597671316400053)
                  ·
                    refine ⟨896011247399781685912505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9557453305597671316400053 896011247399781685912505)
                    ·
                      rfl

theorem cell23_5234927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 5].length) (baseStart_5234927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234927 prefixEnd_5234927 := by exact prefixLift 5234927
  have htrace : WordTrace (prefixWord ++ tailWord_5234927) baseStart_5234927 baseEnd_5234927 := by
    simpa [prefixWord, tailWord_5234927, baseEnd_5234927] using wordTrace_append hprefix tailTrace_5234927
  have hstable : (prefixWord ++ tailWord_5234927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234927).length < 2 ^ (prefixWord ++ tailWord_5234927).sum := by decide
  have hdescent : baseEnd_5234927 < baseStart_5234927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5234943 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_5234943 : Nat := 118140960795 + 5234943 * 2 ^ 59
def prefixEnd_5234943 : Nat := 4983230072969 + 3 ^ 40 * 5234943 * 2
def baseEnd_5234943 : Nat := 2688041957889816995137441

theorem tailTrace_5234943 : CollatzResearch.WordTrace tailWord_5234943 prefixEnd_5234943 2688041957889816995137441 := by
  unfold tailWord_5234943
  simp only [CollatzResearch.WordTrace]
  refine ⟨190934057073703042929989483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127289371382468695286659655 190934057073703042929989483)
  ·
    refine ⟨286401085610554564394984225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190934057073703042929989483 286401085610554564394984225)
    ·
      refine ⟨214800814207915923296238169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286401085610554564394984225 214800814207915923296238169)
      ·
        refine ⟨161100610655936942472178627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214800814207915923296238169 161100610655936942472178627)
        ·
          refine ⟨241650915983905413708267941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161100610655936942472178627 241650915983905413708267941)
          ·
            refine ⟨45309546746982265070300239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241650915983905413708267941 45309546746982265070300239)
            ·
              refine ⟨67964320120473397605450359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45309546746982265070300239 67964320120473397605450359)
              ·
                refine ⟨101946480180710096408175539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67964320120473397605450359 101946480180710096408175539)
                ·
                  refine ⟨152919720271065144612263309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101946480180710096408175539 152919720271065144612263309)
                  ·
                    refine ⟨57344895101649429229598741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152919720271065144612263309 57344895101649429229598741)
                    ·
                      refine ⟨2688041957889816995137441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57344895101649429229598741 2688041957889816995137441)
                      ·
                        rfl

theorem cell23_5234943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_5234943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5234943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5234943 prefixEnd_5234943 := by exact prefixLift 5234943
  have htrace : WordTrace (prefixWord ++ tailWord_5234943) baseStart_5234943 baseEnd_5234943 := by
    simpa [prefixWord, tailWord_5234943, baseEnd_5234943] using wordTrace_append hprefix tailTrace_5234943
  have hstable : (prefixWord ++ tailWord_5234943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5234943).length < 2 ^ (prefixWord ++ tailWord_5234943).sum := by decide
  have hdescent : baseEnd_5234943 < baseStart_5234943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5234943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235003 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 8]
def baseStart_5235003 : Nat := 118140960795 + 5235003 * 2 ^ 59
def prefixEnd_5235003 : Nat := 4983230072969 + 3 ^ 40 * 5235003 * 2
def baseEnd_5235003 : Nat := 2688072766729086760387165

theorem tailTrace_5235003 : CollatzResearch.WordTrace tailWord_5235003 prefixEnd_5235003 2688072766729086760387165 := by
  unfold tailWord_5235003
  simp only [CollatzResearch.WordTrace]
  refine ⟨190936245453485673177173663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127290830302323782118115775 190936245453485673177173663)
  ·
    refine ⟨286404368180228509765760495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190936245453485673177173663 286404368180228509765760495)
    ·
      refine ⟨429606552270342764648640743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286404368180228509765760495 429606552270342764648640743)
      ·
        refine ⟨644409828405514146972961115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429606552270342764648640743 644409828405514146972961115)
        ·
          refine ⟨966614742608271220459441673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644409828405514146972961115 966614742608271220459441673)
          ·
            refine ⟨724961056956203415344581255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966614742608271220459441673 724961056956203415344581255)
            ·
              refine ⟨1087441585434305123016871883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724961056956203415344581255 1087441585434305123016871883)
              ·
                refine ⟨1631162378151457684525307825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087441585434305123016871883 1631162378151457684525307825)
                ·
                  refine ⟨1223371783613593263393980869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1631162378151457684525307825 1223371783613593263393980869)
                  ·
                    refine ⟨229382209427548736886371413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1223371783613593263393980869 229382209427548736886371413)
                    ·
                      refine ⟨2688072766729086760387165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 229382209427548736886371413 2688072766729086760387165)
                      ·
                        rfl

theorem cell23_5235003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_5235003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235003 prefixEnd_5235003 := by exact prefixLift 5235003
  have htrace : WordTrace (prefixWord ++ tailWord_5235003) baseStart_5235003 baseEnd_5235003 := by
    simpa [prefixWord, tailWord_5235003, baseEnd_5235003] using wordTrace_append hprefix tailTrace_5235003
  have hstable : (prefixWord ++ tailWord_5235003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235003).length < 2 ^ (prefixWord ++ tailWord_5235003).sum := by decide
  have hdescent : baseEnd_5235003 < baseStart_5235003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235047 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 1, 6]
def baseStart_5235047 : Nat := 118140960795 + 5235047 * 2 ^ 59
def prefixEnd_5235047 : Nat := 4983230072969 + 3 ^ 40 * 5235047 * 2
def baseEnd_5235047 : Nat := 896031786625961529412321

theorem tailTrace_5235047 : CollatzResearch.WordTrace tailWord_5235047 prefixEnd_5235047 896031786625961529412321 := by
  unfold tailWord_5235047
  simp only [CollatzResearch.WordTrace]
  refine ⟨190937850265326268691775395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127291900176884179127850263 190937850265326268691775395)
  ·
    refine ⟨286406775397989403037663093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190937850265326268691775395 286406775397989403037663093)
    ·
      refine ⟨26850635193561506534780915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 286406775397989403037663093 26850635193561506534780915)
      ·
        refine ⟨40275952790342259802171373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26850635193561506534780915 40275952790342259802171373)
        ·
          refine ⟨15103482296378347425814265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40275952790342259802171373 15103482296378347425814265)
          ·
            refine ⟨11327611722283760569360699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15103482296378347425814265 11327611722283760569360699)
            ·
              refine ⟨16991417583425640854041049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11327611722283760569360699 16991417583425640854041049)
              ·
                refine ⟨12743563187569230640530787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16991417583425640854041049 12743563187569230640530787)
                ·
                  refine ⟨19115344781353845960796181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12743563187569230640530787 19115344781353845960796181)
                  ·
                    refine ⟨896031786625961529412321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19115344781353845960796181 896031786625961529412321)
                    ·
                      rfl

theorem cell23_5235047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_5235047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235047 prefixEnd_5235047 := by exact prefixLift 5235047
  have htrace : WordTrace (prefixWord ++ tailWord_5235047) baseStart_5235047 baseEnd_5235047 := by
    simpa [prefixWord, tailWord_5235047, baseEnd_5235047] using wordTrace_append hprefix tailTrace_5235047
  have hstable : (prefixWord ++ tailWord_5235047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235047).length < 2 ^ (prefixWord ++ tailWord_5235047).sum := by decide
  have hdescent : baseEnd_5235047 < baseStart_5235047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235071 : List Nat := [1, 1, 2, 2, 1, 1, 2, 8, 1, 2, 2]
def baseStart_5235071 : Nat := 118140960795 + 5235071 * 2 ^ 59
def prefixEnd_5235071 : Nat := 4983230072969 + 3 ^ 40 * 5235071 * 2
def baseEnd_5235071 : Nat := 2688107683413592494336853

theorem tailTrace_5235071 : CollatzResearch.WordTrace tailWord_5235071 prefixEnd_5235071 2688107683413592494336853 := by
  unfold tailWord_5235071
  simp only [CollatzResearch.WordTrace]
  refine ⟨190938725617239320790649067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127292483744826213860432711 190938725617239320790649067)
  ·
    refine ⟨286408088425858981185973601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190938725617239320790649067 286408088425858981185973601)
    ·
      refine ⟨214806066319394235889480201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286408088425858981185973601 214806066319394235889480201)
      ·
        refine ⟨161104549739545676917110151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214806066319394235889480201 161104549739545676917110151)
        ·
          refine ⟨241656824609318515375665227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161104549739545676917110151 241656824609318515375665227)
          ·
            refine ⟨362485236913977773063497841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241656824609318515375665227 362485236913977773063497841)
            ·
              refine ⟨271863927685483329797623381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362485236913977773063497841 271863927685483329797623381)
              ·
                refine ⟨3185905402564257771065899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 271863927685483329797623381 3185905402564257771065899)
                ·
                  refine ⟨4778858103846386656598849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3185905402564257771065899 4778858103846386656598849)
                  ·
                    refine ⟨3584143577884789992449137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4778858103846386656598849 3584143577884789992449137)
                    ·
                      refine ⟨2688107683413592494336853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584143577884789992449137 2688107683413592494336853)
                      ·
                        rfl

theorem cell23_5235071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 1, 2, 2].length) (baseStart_5235071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235071 prefixEnd_5235071 := by exact prefixLift 5235071
  have htrace : WordTrace (prefixWord ++ tailWord_5235071) baseStart_5235071 baseEnd_5235071 := by
    simpa [prefixWord, tailWord_5235071, baseEnd_5235071] using wordTrace_append hprefix tailTrace_5235071
  have hstable : (prefixWord ++ tailWord_5235071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235071).length < 2 ^ (prefixWord ++ tailWord_5235071).sum := by decide
  have hdescent : baseEnd_5235071 < baseStart_5235071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235105 : List Nat := [1, 2, 3, 5, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5235105 : Nat := 118140960795 + 5235105 * 2 ^ 59
def prefixEnd_5235105 : Nat := 4983230072969 + 3 ^ 40 * 5235105 * 2
def baseEnd_5235105 : Nat := 2688125141755845361311697

theorem tailTrace_5235105 : CollatzResearch.WordTrace tailWord_5235105 prefixEnd_5235105 2688125141755845361311697 := by
  unfold tailWord_5235105
  simp only [CollatzResearch.WordTrace]
  refine ⟨190939965699116144597386769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127293310466077429731591179 190939965699116144597386769)
  ·
    refine ⟨143204974274337108448040077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190939965699116144597386769 143204974274337108448040077)
    ·
      refine ⟨53701865352876415668015029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143204974274337108448040077 53701865352876415668015029)
      ·
        refine ⟨5034549876832163968876409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53701865352876415668015029 5034549876832163968876409)
        ·
          refine ⟨3775912407624122976657307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5034549876832163968876409 3775912407624122976657307)
          ·
            refine ⟨5663868611436184464985961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3775912407624122976657307 5663868611436184464985961)
            ·
              refine ⟨4247901458577138348739471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5663868611436184464985961 4247901458577138348739471)
              ·
                refine ⟨6371852187865707523109207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4247901458577138348739471 6371852187865707523109207)
                ·
                  refine ⟨9557778281798561284663811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6371852187865707523109207 9557778281798561284663811)
                  ·
                    refine ⟨14336667422697841926995717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9557778281798561284663811 14336667422697841926995717)
                    ·
                      refine ⟨2688125141755845361311697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14336667422697841926995717 2688125141755845361311697)
                      ·
                        rfl

theorem cell23_5235105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5235105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235105 prefixEnd_5235105 := by exact prefixLift 5235105
  have htrace : WordTrace (prefixWord ++ tailWord_5235105) baseStart_5235105 baseEnd_5235105 := by
    simpa [prefixWord, tailWord_5235105, baseEnd_5235105] using wordTrace_append hprefix tailTrace_5235105
  have hstable : (prefixWord ++ tailWord_5235105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235105).length < 2 ^ (prefixWord ++ tailWord_5235105).sum := by decide
  have hdescent : baseEnd_5235105 < baseStart_5235105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235121 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 3]
def baseStart_5235121 : Nat := 118140960795 + 5235121 * 2 ^ 59
def prefixEnd_5235121 : Nat := 4983230072969 + 3 ^ 40 * 5235121 * 2
def baseEnd_5235121 : Nat := 2688133357446317298711623

theorem tailTrace_5235121 : CollatzResearch.WordTrace tailWord_5235121 prefixEnd_5235121 2688133357446317298711623 := by
  unfold tailWord_5235121
  simp only [CollatzResearch.WordTrace]
  refine ⟨190940549267058179329969217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127293699511372119553312811 190940549267058179329969217)
  ·
    refine ⟨143205411950293634497476913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190940549267058179329969217 143205411950293634497476913)
    ·
      refine ⟨107404058962720225873107685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143205411950293634497476913 107404058962720225873107685)
      ·
        refine ⟨20138261055510042351207691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107404058962720225873107685 20138261055510042351207691)
        ·
          refine ⟨30207391583265063526811537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20138261055510042351207691 30207391583265063526811537)
          ·
            refine ⟨22655543687448797645108653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30207391583265063526811537 22655543687448797645108653)
            ·
              refine ⟨8495828882793299116915745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22655543687448797645108653 8495828882793299116915745)
              ·
                refine ⟨6371871662094974337686809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8495828882793299116915745 6371871662094974337686809)
                ·
                  refine ⟨4778903746571230753265107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6371871662094974337686809 4778903746571230753265107)
                  ·
                    refine ⟨7168355619856846129897661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4778903746571230753265107 7168355619856846129897661)
                    ·
                      refine ⟨2688133357446317298711623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7168355619856846129897661 2688133357446317298711623)
                      ·
                        rfl

theorem cell23_5235121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_5235121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235121 prefixEnd_5235121 := by exact prefixLift 5235121
  have htrace : WordTrace (prefixWord ++ tailWord_5235121) baseStart_5235121 baseEnd_5235121 := by
    simpa [prefixWord, tailWord_5235121, baseEnd_5235121] using wordTrace_append hprefix tailTrace_5235121
  have hstable : (prefixWord ++ tailWord_5235121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235121).length < 2 ^ (prefixWord ++ tailWord_5235121).sum := by decide
  have hdescent : baseEnd_5235121 < baseStart_5235121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235148 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 1, 3, 2]
def baseStart_5235148 : Nat := 118140960795 + 5235148 * 2 ^ 59
def prefixEnd_5235148 : Nat := 4983230072969 + 3 ^ 40 * 5235148 * 2
def baseEnd_5235148 : Nat := 2688147221423988693073999

theorem tailTrace_5235148 : CollatzResearch.WordTrace tailWord_5235148 prefixEnd_5235148 2688147221423988693073999 := by
  unfold tailWord_5235148
  simp only [CollatzResearch.WordTrace]
  refine ⟨95470767018980181470601049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127294356025306908627468065 95470767018980181470601049)
  ·
    refine ⟨71603075264235136102950787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95470767018980181470601049 71603075264235136102950787)
    ·
      refine ⟨107404612896352704154426181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71603075264235136102950787 107404612896352704154426181)
      ·
        refine ⟨20138364918066132028954909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107404612896352704154426181 20138364918066132028954909)
        ·
          refine ⟨7551886844274799510858091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20138364918066132028954909 7551886844274799510858091)
          ·
            refine ⟨11327830266412199266287137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7551886844274799510858091 11327830266412199266287137)
            ·
              refine ⟨8495872699809149449715353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11327830266412199266287137 8495872699809149449715353)
              ·
                refine ⟨6371904524856862087286515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8495872699809149449715353 6371904524856862087286515)
                ·
                  refine ⟨9557856787285293130929773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6371904524856862087286515 9557856787285293130929773)
                  ·
                    refine ⟨3584196295231984924098665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9557856787285293130929773 3584196295231984924098665)
                    ·
                      refine ⟨2688147221423988693073999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584196295231984924098665 2688147221423988693073999)
                      ·
                        rfl

theorem cell23_5235148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_5235148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235148 prefixEnd_5235148 := by exact prefixLift 5235148
  have htrace : WordTrace (prefixWord ++ tailWord_5235148) baseStart_5235148 baseEnd_5235148 := by
    simpa [prefixWord, tailWord_5235148, baseEnd_5235148] using wordTrace_append hprefix tailTrace_5235148
  have hstable : (prefixWord ++ tailWord_5235148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235148).length < 2 ^ (prefixWord ++ tailWord_5235148).sum := by decide
  have hdescent : baseEnd_5235148 < baseStart_5235148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235177 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 3]
def baseStart_5235177 : Nat := 118140960795 + 5235177 * 2 ^ 59
def prefixEnd_5235177 : Nat := 4983230072969 + 3 ^ 40 * 5235177 * 2
def baseEnd_5235177 : Nat := 2688162112362969079611365

theorem tailTrace_5235177 : CollatzResearch.WordTrace tailWord_5235177 prefixEnd_5235177 2688162112362969079611365 := by
  unfold tailWord_5235177
  simp only [CollatzResearch.WordTrace]
  refine ⟨190942591754855300894007785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127295061169903533929338523 190942591754855300894007785)
  ·
    refine ⟨143206943816141475670505839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190942591754855300894007785 143206943816141475670505839)
    ·
      refine ⟨214810415724212213505758759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143206943816141475670505839 214810415724212213505758759)
      ·
        refine ⟨322215623586318320258638139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214810415724212213505758759 322215623586318320258638139)
        ·
          refine ⟨483323435379477480387957209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322215623586318320258638139 483323435379477480387957209)
          ·
            refine ⟨362492576534608110290967907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483323435379477480387957209 362492576534608110290967907)
            ·
              refine ⟨543738864801912165436451861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362492576534608110290967907 543738864801912165436451861)
              ·
                refine ⟨25487759287589632754833681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 543738864801912165436451861 25487759287589632754833681)
                ·
                  refine ⟨19115819465692224566125261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25487759287589632754833681 19115819465692224566125261)
                  ·
                    refine ⟨7168432299634584212296973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19115819465692224566125261 7168432299634584212296973)
                    ·
                      refine ⟨2688162112362969079611365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7168432299634584212296973 2688162112362969079611365)
                      ·
                        rfl

theorem cell23_5235177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 3, 3].length) (baseStart_5235177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235177 prefixEnd_5235177 := by exact prefixLift 5235177
  have htrace : WordTrace (prefixWord ++ tailWord_5235177) baseStart_5235177 baseEnd_5235177 := by
    simpa [prefixWord, tailWord_5235177, baseEnd_5235177] using wordTrace_append hprefix tailTrace_5235177
  have hstable : (prefixWord ++ tailWord_5235177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235177).length < 2 ^ (prefixWord ++ tailWord_5235177).sum := by decide
  have hdescent : baseEnd_5235177 < baseStart_5235177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235197 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_5235197 : Nat := 118140960795 + 5235197 * 2 ^ 59
def prefixEnd_5235197 : Nat := 4983230072969 + 3 ^ 40 * 5235197 * 2
def baseEnd_5235197 : Nat := 896057460658686333787091

theorem tailTrace_5235197 : CollatzResearch.WordTrace tailWord_5235197 prefixEnd_5235197 896057460658686333787091 := by
  unfold tailWord_5235197
  simp only [CollatzResearch.WordTrace]
  refine ⟨190943321214782844309735845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127295547476521896206490563 190943321214782844309735845)
  ·
    refine ⟨35801872727771783308075471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190943321214782844309735845 35801872727771783308075471)
    ·
      refine ⟨53702809091657674962113207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35801872727771783308075471 53702809091657674962113207)
      ·
        refine ⟨80554213637486512443169811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53702809091657674962113207 80554213637486512443169811)
        ·
          refine ⟨120831320456229768664754717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80554213637486512443169811 120831320456229768664754717)
          ·
            refine ⟨45311745171086163249283019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120831320456229768664754717 45311745171086163249283019)
            ·
              refine ⟨67967617756629244873924529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45311745171086163249283019 67967617756629244873924529)
              ·
                refine ⟨50975713317471933655443397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67967617756629244873924529 50975713317471933655443397)
                ·
                  refine ⟨9557946247025987560395637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50975713317471933655443397 9557946247025987560395637)
                  ·
                    refine ⟨896057460658686333787091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9557946247025987560395637 896057460658686333787091)
                    ·
                      rfl

theorem cell23_5235197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_5235197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235197 prefixEnd_5235197 := by exact prefixLift 5235197
  have htrace : WordTrace (prefixWord ++ tailWord_5235197) baseStart_5235197 baseEnd_5235197 := by
    simpa [prefixWord, tailWord_5235197, baseEnd_5235197] using wordTrace_append hprefix tailTrace_5235197
  have hstable : (prefixWord ++ tailWord_5235197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235197).length < 2 ^ (prefixWord ++ tailWord_5235197).sum := by decide
  have hdescent : baseEnd_5235197 < baseStart_5235197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235214 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_5235214 : Nat := 118140960795 + 5235214 * 2 ^ 59
def prefixEnd_5235214 : Nat := 4983230072969 + 3 ^ 40 * 5235214 * 2
def baseEnd_5235214 : Nat := 896060370382395144949565

theorem tailTrace_5235214 : CollatzResearch.WordTrace tailWord_5235214 prefixEnd_5235214 896060370382395144949565 := by
  unfold tailWord_5235214
  simp only [CollatzResearch.WordTrace]
  refine ⟨23867992656965157026638087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127295960837147504142069797 23867992656965157026638087)
  ·
    refine ⟨35801988985447735539957131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23867992656965157026638087 35801988985447735539957131)
    ·
      refine ⟨53702983478171603309935697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35801988985447735539957131 53702983478171603309935697)
      ·
        refine ⟨40277237608628702482451773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53702983478171603309935697 40277237608628702482451773)
        ·
          refine ⟨15103964103235763430919415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40277237608628702482451773 15103964103235763430919415)
          ·
            refine ⟨22655946154853645146379123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15103964103235763430919415 22655946154853645146379123)
            ·
              refine ⟨33983919232280467719568685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22655946154853645146379123 33983919232280467719568685)
              ·
                refine ⟨12743969712105175394838257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33983919232280467719568685 12743969712105175394838257)
                ·
                  refine ⟨9557977284078881546128693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12743969712105175394838257 9557977284078881546128693)
                  ·
                    refine ⟨896060370382395144949565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9557977284078881546128693 896060370382395144949565)
                    ·
                      rfl

theorem cell23_5235214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_5235214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235214 prefixEnd_5235214 := by exact prefixLift 5235214
  have htrace : WordTrace (prefixWord ++ tailWord_5235214) baseStart_5235214 baseEnd_5235214 := by
    simpa [prefixWord, tailWord_5235214, baseEnd_5235214] using wordTrace_append hprefix tailTrace_5235214
  have hstable : (prefixWord ++ tailWord_5235214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235214).length < 2 ^ (prefixWord ++ tailWord_5235214).sum := by decide
  have hdescent : baseEnd_5235214 < baseStart_5235214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235245 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5235245 : Nat := 118140960795 + 5235245 * 2 ^ 59
def prefixEnd_5235245 : Nat := 4983230072969 + 3 ^ 40 * 5235245 * 2
def baseEnd_5235245 : Nat := 2688197029047474813561053

theorem tailTrace_5235245 : CollatzResearch.WordTrace tailWord_5235245 prefixEnd_5235245 2688197029047474813561053 := by
  unfold tailWord_5235245
  simp only [CollatzResearch.WordTrace]
  refine ⟨190945071918608948507483189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127296714612405965671655459 190945071918608948507483189)
  ·
    refine ⟨17901100492369588922576549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190945071918608948507483189 17901100492369588922576549)
    ·
      refine ⟨3356456342319297922983103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17901100492369588922576549 3356456342319297922983103)
      ·
        refine ⟨5034684513478946884474655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356456342319297922983103 5034684513478946884474655)
        ·
          refine ⟨7552026770218420326711983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5034684513478946884474655 7552026770218420326711983)
          ·
            refine ⟨11328040155327630490067975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7552026770218420326711983 11328040155327630490067975)
            ·
              refine ⟨16992060232991445735101963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11328040155327630490067975 16992060232991445735101963)
              ·
                refine ⟨25488090349487168602652945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16992060232991445735101963 25488090349487168602652945)
                ·
                  refine ⟨19116067762115376451989709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25488090349487168602652945 19116067762115376451989709)
                  ·
                    refine ⟨7168525410793266169496141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19116067762115376451989709 7168525410793266169496141)
                    ·
                      refine ⟨2688197029047474813561053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7168525410793266169496141 2688197029047474813561053)
                      ·
                        rfl

theorem cell23_5235245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5235245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235245 prefixEnd_5235245 := by exact prefixLift 5235245
  have htrace : WordTrace (prefixWord ++ tailWord_5235245) baseStart_5235245 baseEnd_5235245 := by
    simpa [prefixWord, tailWord_5235245, baseEnd_5235245] using wordTrace_append hprefix tailTrace_5235245
  have hstable : (prefixWord ++ tailWord_5235245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235245).length < 2 ^ (prefixWord ++ tailWord_5235245).sum := by decide
  have hdescent : baseEnd_5235245 < baseStart_5235245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235261 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_5235261 : Nat := 118140960795 + 5235261 * 2 ^ 59
def prefixEnd_5235261 : Nat := 4983230072969 + 3 ^ 40 * 5235261 * 2
def baseEnd_5235261 : Nat := 896068414912648916986993

theorem tailTrace_5235261 : CollatzResearch.WordTrace tailWord_5235261 prefixEnd_5235261 896068414912648916986993 := by
  unfold tailWord_5235261
  simp only [CollatzResearch.WordTrace]
  refine ⟨190945655486550983240065637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127297103657700655493377091 190945655486550983240065637)
  ·
    refine ⟨35802310403728309357512307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190945655486550983240065637 35802310403728309357512307)
    ·
      refine ⟨53703465605592464036268461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35802310403728309357512307 53703465605592464036268461)
      ·
        refine ⟨20138799602097174013600673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53703465605592464036268461 20138799602097174013600673)
        ·
          refine ⟨15104099701572880510200505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20138799602097174013600673 15104099701572880510200505)
          ·
            refine ⟨11328074776179660382650379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15104099701572880510200505 11328074776179660382650379)
            ·
              refine ⟨16992112164269490573975569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11328074776179660382650379 16992112164269490573975569)
              ·
                refine ⟨12744084123202117930481677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16992112164269490573975569 12744084123202117930481677)
                ·
                  refine ⟨4779031546200794223930629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12744084123202117930481677 4779031546200794223930629)
                  ·
                    refine ⟨896068414912648916986993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4779031546200794223930629 896068414912648916986993)
                    ·
                      rfl

theorem cell23_5235261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_5235261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235261 prefixEnd_5235261 := by exact prefixLift 5235261
  have htrace : WordTrace (prefixWord ++ tailWord_5235261) baseStart_5235261 baseEnd_5235261 := by
    simpa [prefixWord, tailWord_5235261, baseEnd_5235261] using wordTrace_append hprefix tailTrace_5235261
  have hstable : (prefixWord ++ tailWord_5235261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235261).length < 2 ^ (prefixWord ++ tailWord_5235261).sum := by decide
  have hdescent : baseEnd_5235261 < baseStart_5235261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235271 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_5235271 : Nat := 118140960795 + 5235271 * 2 ^ 59
def prefixEnd_5235271 : Nat := 4983230072969 + 3 ^ 40 * 5235271 * 2
def baseEnd_5235271 : Nat := 2688210379544491711835933

theorem tailTrace_5235271 : CollatzResearch.WordTrace tailWord_5235271 prefixEnd_5235271 2688210379544491711835933 := by
  unfold tailWord_5235271
  simp only [CollatzResearch.WordTrace]
  refine ⟨190946020216514754947929667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127297346811009836631953111 190946020216514754947929667)
  ·
    refine ⟨286419030324772132421894501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190946020216514754947929667 286419030324772132421894501)
    ·
      refine ⟨53703568185894774829105219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286419030324772132421894501 53703568185894774829105219)
      ·
        refine ⟨80555352278842162243657829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53703568185894774829105219 80555352278842162243657829)
        ·
          refine ⟨15104128552282905420685843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80555352278842162243657829 15104128552282905420685843)
          ·
            refine ⟨22656192828424358131028765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15104128552282905420685843 22656192828424358131028765)
            ·
              refine ⟨8496072310659134299135787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22656192828424358131028765 8496072310659134299135787)
              ·
                refine ⟨12744108465988701448703681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8496072310659134299135787 12744108465988701448703681)
                ·
                  refine ⟨9558081349491526086527761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12744108465988701448703681 9558081349491526086527761)
                  ·
                    refine ⟨7168561012118644564895821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9558081349491526086527761 7168561012118644564895821)
                    ·
                      refine ⟨2688210379544491711835933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7168561012118644564895821 2688210379544491711835933)
                      ·
                        rfl

theorem cell23_5235271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_5235271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235271 prefixEnd_5235271 := by exact prefixLift 5235271
  have htrace : WordTrace (prefixWord ++ tailWord_5235271) baseStart_5235271 baseEnd_5235271 := by
    simpa [prefixWord, tailWord_5235271, baseEnd_5235271] using wordTrace_append hprefix tailTrace_5235271
  have hstable : (prefixWord ++ tailWord_5235271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235271).length < 2 ^ (prefixWord ++ tailWord_5235271).sum := by decide
  have hdescent : baseEnd_5235271 < baseStart_5235271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235307 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 4]
def baseStart_5235307 : Nat := 118140960795 + 5235307 * 2 ^ 59
def prefixEnd_5235307 : Nat := 4983230072969 + 3 ^ 40 * 5235307 * 2
def baseEnd_5235307 : Nat := 2688228864848053570985767

theorem tailTrace_5235307 : CollatzResearch.WordTrace tailWord_5235307 prefixEnd_5235307 2688228864848053570985767 := by
  unfold tailWord_5235307
  simp only [CollatzResearch.WordTrace]
  refine ⟨190947333244384333096240175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127298222162922888730826783 190947333244384333096240175)
  ·
    refine ⟨286420999866576499644360263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190947333244384333096240175 286420999866576499644360263)
    ·
      refine ⟨429631499799864749466540395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286420999866576499644360263 429631499799864749466540395)
      ·
        refine ⟨644447249699797124199810593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429631499799864749466540395 644447249699797124199810593)
        ·
          refine ⟨483335437274847843149857945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644447249699797124199810593 483335437274847843149857945)
          ·
            refine ⟨362501577956135882362393459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483335437274847843149857945 362501577956135882362393459)
            ·
              refine ⟨543752366934203823543590189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362501577956135882362393459 543752366934203823543590189)
              ·
                refine ⟨203907137600326433828846321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 543752366934203823543590189 203907137600326433828846321)
                ·
                  refine ⟨152930353200244825371634741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203907137600326433828846321 152930353200244825371634741)
                  ·
                    refine ⟨14337220612522952378590757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 152930353200244825371634741 14337220612522952378590757)
                    ·
                      refine ⟨2688228864848053570985767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14337220612522952378590757 2688228864848053570985767)
                      ·
                        rfl

theorem cell23_5235307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 4].length) (baseStart_5235307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235307 prefixEnd_5235307 := by exact prefixLift 5235307
  have htrace : WordTrace (prefixWord ++ tailWord_5235307) baseStart_5235307 baseEnd_5235307 := by
    simpa [prefixWord, tailWord_5235307, baseEnd_5235307] using wordTrace_append hprefix tailTrace_5235307
  have hstable : (prefixWord ++ tailWord_5235307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235307).length < 2 ^ (prefixWord ++ tailWord_5235307).sum := by decide
  have hdescent : baseEnd_5235307 < baseStart_5235307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235321 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 1, 5]
def baseStart_5235321 : Nat := 118140960795 + 5235321 * 2 ^ 59
def prefixEnd_5235321 : Nat := 4983230072969 + 3 ^ 40 * 5235321 * 2
def baseEnd_5235321 : Nat := 896078684525738838736901

theorem tailTrace_5235321 : CollatzResearch.WordTrace tailWord_5235321 prefixEnd_5235321 896078684525738838736901 := by
  unfold tailWord_5235321
  simp only [CollatzResearch.WordTrace]
  refine ⟨190947843866333613487249817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127298562577555742324833211 190947843866333613487249817)
  ·
    refine ⟨143210882899750210115437363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190947843866333613487249817 143210882899750210115437363)
    ·
      refine ⟨214816324349625315173156045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143210882899750210115437363 214816324349625315173156045)
      ·
        refine ⟨80556121631109493189933517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214816324349625315173156045 80556121631109493189933517)
        ·
          refine ⟨30208545611666059946225069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80556121631109493189933517 30208545611666059946225069)
          ·
            refine ⟨11328204604374772479834401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30208545611666059946225069 11328204604374772479834401)
            ·
              refine ⟨8496153453281079359875801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11328204604374772479834401 8496153453281079359875801)
              ·
                refine ⟨6372115089960809519906851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8496153453281079359875801 6372115089960809519906851)
                ·
                  refine ⟨9558172634941214279860277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6372115089960809519906851 9558172634941214279860277)
                  ·
                    refine ⟨896078684525738838736901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9558172634941214279860277 896078684525738838736901)
                    ·
                      rfl

theorem cell23_5235321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 5].length) (baseStart_5235321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235321 prefixEnd_5235321 := by exact prefixLift 5235321
  have htrace : WordTrace (prefixWord ++ tailWord_5235321) baseStart_5235321 baseEnd_5235321 := by
    simpa [prefixWord, tailWord_5235321, baseEnd_5235321] using wordTrace_append hprefix tailTrace_5235321
  have hstable : (prefixWord ++ tailWord_5235321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235321).length < 2 ^ (prefixWord ++ tailWord_5235321).sum := by decide
  have hdescent : baseEnd_5235321 < baseStart_5235321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235324 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_5235324 : Nat := 118140960795 + 5235324 * 2 ^ 59
def prefixEnd_5235324 : Nat := 4983230072969 + 3 ^ 40 * 5235324 * 2
def baseEnd_5235324 : Nat := 2688237594019180004473189

theorem tailTrace_5235324 : CollatzResearch.WordTrace tailWord_5235324 prefixEnd_5235324 2688237594019180004473189 := by
  unfold tailWord_5235324
  simp only [CollatzResearch.WordTrace]
  refine ⟨95473976642661372499804513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127298635523548496666406017 95473976642661372499804513)
  ·
    refine ⟨71605482481996029374853385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95473976642661372499804513 71605482481996029374853385)
    ·
      refine ⟨53704111861497022031140039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71605482481996029374853385 53704111861497022031140039)
      ·
        refine ⟨80556167792245533046710059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53704111861497022031140039 80556167792245533046710059)
        ·
          refine ⟨120834251688368299570065089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80556167792245533046710059 120834251688368299570065089)
          ·
            refine ⟨90625688766276224677548817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120834251688368299570065089 90625688766276224677548817)
            ·
              refine ⟨67969266574707168508161613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90625688766276224677548817 67969266574707168508161613)
              ·
                refine ⟨25488474965515188190560605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67969266574707168508161613 25488474965515188190560605)
                ·
                  refine ⟨9558178112068195571460227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25488474965515188190560605 9558178112068195571460227)
                  ·
                    refine ⟨14337267168102293357190341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9558178112068195571460227 14337267168102293357190341)
                    ·
                      refine ⟨2688237594019180004473189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14337267168102293357190341 2688237594019180004473189)
                      ·
                        rfl

theorem cell23_5235324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_5235324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235324 prefixEnd_5235324 := by exact prefixLift 5235324
  have htrace : WordTrace (prefixWord ++ tailWord_5235324) baseStart_5235324 baseEnd_5235324 := by
    simpa [prefixWord, tailWord_5235324, baseEnd_5235324] using wordTrace_append hprefix tailTrace_5235324
  have hstable : (prefixWord ++ tailWord_5235324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235324).length < 2 ^ (prefixWord ++ tailWord_5235324).sum := by decide
  have hdescent : baseEnd_5235324 < baseStart_5235324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235344 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3]
def baseStart_5235344 : Nat := 118140960795 + 5235344 * 2 ^ 59
def prefixEnd_5235344 : Nat := 4983230072969 + 3 ^ 40 * 5235344 * 2
def baseEnd_5235344 : Nat := 2688247863632269926223097

theorem tailTrace_5235344 : CollatzResearch.WordTrace tailWord_5235344 prefixEnd_5235344 2688247863632269926223097 := by
  unfold tailWord_5235344
  simp only [CollatzResearch.WordTrace]
  refine ⟨95474341372625144207668543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127299121830166858943558057 95474341372625144207668543)
  ·
    refine ⟨143211512058937716311502815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95474341372625144207668543 143211512058937716311502815)
    ·
      refine ⟨214817268088406574467254223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143211512058937716311502815 214817268088406574467254223)
      ·
        refine ⟨322225902132609861700881335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214817268088406574467254223 322225902132609861700881335)
        ·
          refine ⟨483338853198914792551322003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322225902132609861700881335 483338853198914792551322003)
          ·
            refine ⟨725008279798372188826983005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483338853198914792551322003 725008279798372188826983005)
            ·
              refine ⟨271878104924389570810118627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725008279798372188826983005 271878104924389570810118627)
              ·
                refine ⟨407817157386584356215177941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271878104924389570810118627 407817157386584356215177941)
                ·
                  refine ⟨9558214626248070848793233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 407817157386584356215177941 9558214626248070848793233)
                  ·
                    refine ⟨7168660969686053136594925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9558214626248070848793233 7168660969686053136594925)
                    ·
                      refine ⟨2688247863632269926223097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7168660969686053136594925 2688247863632269926223097)
                      ·
                        rfl

theorem cell23_5235344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_5235344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235344 prefixEnd_5235344 := by exact prefixLift 5235344
  have htrace : WordTrace (prefixWord ++ tailWord_5235344) baseStart_5235344 baseEnd_5235344 := by
    simpa [prefixWord, tailWord_5235344, baseEnd_5235344] using wordTrace_append hprefix tailTrace_5235344
  have hstable : (prefixWord ++ tailWord_5235344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235344).length < 2 ^ (prefixWord ++ tailWord_5235344).sum := by decide
  have hdescent : baseEnd_5235344 < baseStart_5235344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235351 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 2, 4]
def baseStart_5235351 : Nat := 118140960795 + 5235351 * 2 ^ 59
def prefixEnd_5235351 : Nat := 4983230072969 + 3 ^ 40 * 5235351 * 2
def baseEnd_5235351 : Nat := 896083819332283799611855

theorem tailTrace_5235351 : CollatzResearch.WordTrace tailWord_5235351 prefixEnd_5235351 896083819332283799611855 := by
  unfold tailWord_5235351
  simp only [CollatzResearch.WordTrace]
  refine ⟨190948938056224928610841907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127299292037483285740561271 190948938056224928610841907)
  ·
    refine ⟨286423407084337392916262861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190948938056224928610841907 286423407084337392916262861)
    ·
      refine ⟨107408777656626522343598573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286423407084337392916262861 107408777656626522343598573)
      ·
        refine ⟨40278291621234945878849465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107408777656626522343598573 40278291621234945878849465)
        ·
          refine ⟨30208718715926209409137099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40278291621234945878849465 30208718715926209409137099)
          ·
            refine ⟨45313078073889314113705649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30208718715926209409137099 45313078073889314113705649)
            ·
              refine ⟨33984808555416985585279237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45313078073889314113705649 33984808555416985585279237)
              ·
                refine ⟨6372151604140684797239857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33984808555416985585279237 6372151604140684797239857)
                ·
                  refine ⟨4779113703105513597929893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6372151604140684797239857 4779113703105513597929893)
                  ·
                    refine ⟨896083819332283799611855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4779113703105513597929893 896083819332283799611855)
                    ·
                      rfl

theorem cell23_5235351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_5235351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235351 prefixEnd_5235351 := by exact prefixLift 5235351
  have htrace : WordTrace (prefixWord ++ tailWord_5235351) baseStart_5235351 baseEnd_5235351 := by
    simpa [prefixWord, tailWord_5235351, baseEnd_5235351] using wordTrace_append hprefix tailTrace_5235351
  have hstable : (prefixWord ++ tailWord_5235351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235351).length < 2 ^ (prefixWord ++ tailWord_5235351).sum := by decide
  have hdescent : baseEnd_5235351 < baseStart_5235351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235364 : List Nat := [2, 3, 1, 2, 2, 1, 4, 8]
def baseStart_5235364 : Nat := 118140960795 + 5235364 * 2 ^ 59
def prefixEnd_5235364 : Nat := 4983230072969 + 3 ^ 40 * 5235364 * 2
def baseEnd_5235364 : Nat := 99565116046124438813815

theorem tailTrace_5235364 : CollatzResearch.WordTrace tailWord_5235364 prefixEnd_5235364 99565116046124438813815 := by
  unfold tailWord_5235364
  simp only [CollatzResearch.WordTrace]
  refine ⟨95474706102588915915532573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127299608136785221220710097 95474706102588915915532573)
  ·
    refine ⟨35803014788470843468324715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95474706102588915915532573 35803014788470843468324715)
    ·
      refine ⟨53704522182706265202487073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35803014788470843468324715 53704522182706265202487073)
      ·
        refine ⟨40278391637029698901865305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53704522182706265202487073 40278391637029698901865305)
        ·
          refine ⟨30208793727772274176398979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40278391637029698901865305 30208793727772274176398979)
          ·
            refine ⟨45313190591658411264598469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30208793727772274176398979 45313190591658411264598469)
            ·
              refine ⟨8496223235935952112112213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45313190591658411264598469 8496223235935952112112213)
              ·
                refine ⟨99565116046124438813815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8496223235935952112112213 99565116046124438813815)
                ·
                  rfl

theorem cell23_5235364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 8].length) (baseStart_5235364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235364 prefixEnd_5235364 := by exact prefixLift 5235364
  have htrace : WordTrace (prefixWord ++ tailWord_5235364) baseStart_5235364 baseEnd_5235364 := by
    simpa [prefixWord, tailWord_5235364, baseEnd_5235364] using wordTrace_append hprefix tailTrace_5235364
  have hstable : (prefixWord ++ tailWord_5235364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235364).length < 2 ^ (prefixWord ++ tailWord_5235364).sum := by decide
  have hdescent : baseEnd_5235364 < baseStart_5235364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235391 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 3]
def baseStart_5235391 : Nat := 118140960795 + 5235391 * 2 ^ 59
def prefixEnd_5235391 : Nat := 4983230072969 + 3 ^ 40 * 5235391 * 2
def baseEnd_5235391 : Nat := 2688271997223031242335381

theorem tailTrace_5235391 : CollatzResearch.WordTrace tailWord_5235391 prefixEnd_5235391 2688271997223031242335381 := by
  unfold tailWord_5235391
  simp only [CollatzResearch.WordTrace]
  refine ⟨190950396976080015442298027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127300264650720010294865351 190950396976080015442298027)
  ·
    refine ⟨286425595464120023163447041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190950396976080015442298027 286425595464120023163447041)
    ·
      refine ⟨214819196598090017372585281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286425595464120023163447041 214819196598090017372585281)
      ·
        refine ⟨161114397448567513029438961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214819196598090017372585281 161114397448567513029438961)
        ·
          refine ⟨120835798086425634772079221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161114397448567513029438961 120835798086425634772079221)
          ·
            refine ⟨11328356070602403259882427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120835798086425634772079221 11328356070602403259882427)
            ·
              refine ⟨16992534105903604889823641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11328356070602403259882427 16992534105903604889823641)
              ·
                refine ⟨12744400579427703667367731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16992534105903604889823641 12744400579427703667367731)
                ·
                  refine ⟨19116600869141555501051597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12744400579427703667367731 19116600869141555501051597)
                  ·
                    refine ⟨7168725325928083312894349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19116600869141555501051597 7168725325928083312894349)
                    ·
                      refine ⟨2688271997223031242335381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7168725325928083312894349 2688271997223031242335381)
                      ·
                        rfl

theorem cell23_5235391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_5235391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235391 prefixEnd_5235391 := by exact prefixLift 5235391
  have htrace : WordTrace (prefixWord ++ tailWord_5235391) baseStart_5235391 baseEnd_5235391 := by
    simpa [prefixWord, tailWord_5235391, baseEnd_5235391] using wordTrace_append hprefix tailTrace_5235391
  have hstable : (prefixWord ++ tailWord_5235391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235391).length < 2 ^ (prefixWord ++ tailWord_5235391).sum := by decide
  have hdescent : baseEnd_5235391 < baseStart_5235391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235398 : List Nat := [6, 1, 2, 1, 2, 11]
def baseStart_5235398 : Nat := 118140960795 + 5235398 * 2 ^ 59
def prefixEnd_5235398 : Nat := 4983230072969 + 3 ^ 40 * 5235398 * 2
def baseEnd_5235398 : Nat := 11062862516821451501843

theorem tailTrace_5235398 : CollatzResearch.WordTrace tailWord_5235398 prefixEnd_5235398 11062862516821451501843 := by
  unfold tailWord_5235398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5967207883970457988681339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 127300434858036437091868565 5967207883970457988681339)
  ·
    refine ⟨8950811825955686983022009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5967207883970457988681339 8950811825955686983022009)
    ·
      refine ⟨6713108869466765237266507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8950811825955686983022009 6713108869466765237266507)
      ·
        refine ⟨10069663304200147855899761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6713108869466765237266507 10069663304200147855899761)
        ·
          refine ⟨7552247478150110891924821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10069663304200147855899761 7552247478150110891924821)
          ·
            refine ⟨11062862516821451501843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7552247478150110891924821 11062862516821451501843)
            ·
              rfl

theorem cell23_5235398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 11].length) (baseStart_5235398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235398 prefixEnd_5235398 := by exact prefixLift 5235398
  have htrace : WordTrace (prefixWord ++ tailWord_5235398) baseStart_5235398 baseEnd_5235398 := by
    simpa [prefixWord, tailWord_5235398, baseEnd_5235398] using wordTrace_append hprefix tailTrace_5235398
  have hstable : (prefixWord ++ tailWord_5235398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235398).length < 2 ^ (prefixWord ++ tailWord_5235398).sum := by decide
  have hdescent : baseEnd_5235398 < baseStart_5235398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235448 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 4, 2, 2]
def baseStart_5235448 : Nat := 118140960795 + 5235448 * 2 ^ 59
def prefixEnd_5235448 : Nat := 4983230072969 + 3 ^ 40 * 5235448 * 2
def baseEnd_5235448 : Nat := 2688301265620337519322619

theorem tailTrace_5235448 : CollatzResearch.WordTrace tailWord_5235448 prefixEnd_5235448 2688301265620337519322619 := by
  unfold tailWord_5235448
  simp only [CollatzResearch.WordTrace]
  refine ⟨95476237968436757088561499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127301650624582342784748665 95476237968436757088561499)
  ·
    refine ⟨143214356952655135632842249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95476237968436757088561499 143214356952655135632842249)
    ·
      refine ⟨107410767714491351724631687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143214356952655135632842249 107410767714491351724631687)
      ·
        refine ⟨161116151571737027586947531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107410767714491351724631687 161116151571737027586947531)
        ·
          refine ⟨241674227357605541380421297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161116151571737027586947531 241674227357605541380421297)
          ·
            refine ⟨181255670518204156035315973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241674227357605541380421297 181255670518204156035315973)
            ·
              refine ⟨33985438222163279256621745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 181255670518204156035315973 33985438222163279256621745)
              ·
                refine ⟨25489078666622459442466309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33985438222163279256621745 25489078666622459442466309)
                ·
                  refine ⟨4779202249991711145462433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25489078666622459442466309 4779202249991711145462433)
                  ·
                    refine ⟨3584401687493783359096825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779202249991711145462433 3584401687493783359096825)
                    ·
                      refine ⟨2688301265620337519322619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584401687493783359096825 2688301265620337519322619)
                      ·
                        rfl

theorem cell23_5235448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_5235448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235448 prefixEnd_5235448 := by exact prefixLift 5235448
  have htrace : WordTrace (prefixWord ++ tailWord_5235448) baseStart_5235448 baseEnd_5235448 := by
    simpa [prefixWord, tailWord_5235448, baseEnd_5235448] using wordTrace_append hprefix tailTrace_5235448
  have hstable : (prefixWord ++ tailWord_5235448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235448).length < 2 ^ (prefixWord ++ tailWord_5235448).sum := by decide
  have hdescent : baseEnd_5235448 < baseStart_5235448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235452 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_5235452 : Nat := 118140960795 + 5235452 * 2 ^ 59
def prefixEnd_5235452 : Nat := 4983230072969 + 3 ^ 40 * 5235452 * 2
def baseEnd_5235452 : Nat := 2688303319542955503672601

theorem tailTrace_5235452 : CollatzResearch.WordTrace tailWord_5235452 prefixEnd_5235452 2688303319542955503672601 := by
  unfold tailWord_5235452
  simp only [CollatzResearch.WordTrace]
  refine ⟨95476310914429511430134305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127301747885906015240179073 95476310914429511430134305)
  ·
    refine ⟨71607233185822133572600729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95476310914429511430134305 71607233185822133572600729)
    ·
      refine ⟨53705424889366600179450547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71607233185822133572600729 53705424889366600179450547)
      ·
        refine ⟨80558137334049900269175821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53705424889366600179450547 80558137334049900269175821)
        ·
          refine ⟨30209301500268712600940933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80558137334049900269175821 30209301500268712600940933)
          ·
            refine ⟨5664244031300383612676425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30209301500268712600940933 5664244031300383612676425)
            ·
              refine ⟨4248183023475287709507319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5664244031300383612676425 4248183023475287709507319)
              ·
                refine ⟨6372274535212931564260979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248183023475287709507319 6372274535212931564260979)
                ·
                  refine ⟨9558411802819397346391469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6372274535212931564260979 9558411802819397346391469)
                  ·
                    refine ⟨3584404426057274004896801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9558411802819397346391469 3584404426057274004896801)
                    ·
                      refine ⟨2688303319542955503672601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584404426057274004896801 2688303319542955503672601)
                      ·
                        rfl

theorem cell23_5235452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_5235452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235452 prefixEnd_5235452 := by exact prefixLift 5235452
  have htrace : WordTrace (prefixWord ++ tailWord_5235452) baseStart_5235452 baseEnd_5235452 := by
    simpa [prefixWord, tailWord_5235452, baseEnd_5235452] using wordTrace_append hprefix tailTrace_5235452
  have hstable : (prefixWord ++ tailWord_5235452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235452).length < 2 ^ (prefixWord ++ tailWord_5235452).sum := by decide
  have hdescent : baseEnd_5235452 < baseStart_5235452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235465 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 2, 2, 2]
def baseStart_5235465 : Nat := 118140960795 + 5235465 * 2 ^ 59
def prefixEnd_5235465 : Nat := 4983230072969 + 3 ^ 40 * 5235465 * 2
def baseEnd_5235465 : Nat := 2688309994791463952810041

theorem tailTrace_5235465 : CollatzResearch.WordTrace tailWord_5235465 prefixEnd_5235465 2688309994791463952810041 := by
  unfold tailWord_5235465
  simp only [CollatzResearch.WordTrace]
  refine ⟨190953095977811926080491849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127302063985207950720327899 190953095977811926080491849)
  ·
    refine ⟨143214821983358944560368887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190953095977811926080491849 143214821983358944560368887)
    ·
      refine ⟨214822232975038416840553331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143214821983358944560368887 214822232975038416840553331)
      ·
        refine ⟨322233349462557625260829997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214822232975038416840553331 322233349462557625260829997)
        ·
          refine ⟨120837506048459109472811249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322233349462557625260829997 120837506048459109472811249)
          ·
            refine ⟨90628129536344332104608437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120837506048459109472811249 90628129536344332104608437)
            ·
              refine ⟨8496387144032281134807041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90628129536344332104608437 8496387144032281134807041)
              ·
                refine ⟨6372290358024210851105281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8496387144032281134807041 6372290358024210851105281)
                ·
                  refine ⟨4779217768518158138328961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6372290358024210851105281 4779217768518158138328961)
                  ·
                    refine ⟨3584413326388618603746721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779217768518158138328961 3584413326388618603746721)
                    ·
                      refine ⟨2688309994791463952810041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584413326388618603746721 2688309994791463952810041)
                      ·
                        rfl

theorem cell23_5235465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 2, 2].length) (baseStart_5235465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235465 prefixEnd_5235465 := by exact prefixLift 5235465
  have htrace : WordTrace (prefixWord ++ tailWord_5235465) baseStart_5235465 baseEnd_5235465 := by
    simpa [prefixWord, tailWord_5235465, baseEnd_5235465] using wordTrace_append hprefix tailTrace_5235465
  have hstable : (prefixWord ++ tailWord_5235465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235465).length < 2 ^ (prefixWord ++ tailWord_5235465).sum := by decide
  have hdescent : baseEnd_5235465 < baseStart_5235465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235471 : List Nat := [1, 1, 2, 1, 1, 1, 5, 6, 5]
def baseStart_5235471 : Nat := 118140960795 + 5235471 * 2 ^ 59
def prefixEnd_5235471 : Nat := 4983230072969 + 3 ^ 40 * 5235471 * 2
def baseEnd_5235471 : Nat := 298701452852821214370557

theorem tailTrace_5235471 : CollatzResearch.WordTrace tailWord_5235471 prefixEnd_5235471 298701452852821214370557 := by
  unfold tailWord_5235471
  simp only [CollatzResearch.WordTrace]
  refine ⟨190953314815790189105210267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127302209877193459403473511 190953314815790189105210267)
  ·
    refine ⟨286429972223685283657815401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190953314815790189105210267 286429972223685283657815401)
    ·
      refine ⟨214822479167763962743361551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286429972223685283657815401 214822479167763962743361551)
      ·
        refine ⟨322233718751645944115042327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214822479167763962743361551 322233718751645944115042327)
        ·
          refine ⟨483350578127468916172563491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322233718751645944115042327 483350578127468916172563491)
          ·
            refine ⟨725025867191203374258845237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483350578127468916172563491 725025867191203374258845237)
            ·
              refine ⟨67971175049175316336766741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 725025867191203374258845237 67971175049175316336766741)
              ·
                refine ⟨3186148830430092953285941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67971175049175316336766741 3186148830430092953285941)
                ·
                  refine ⟨298701452852821214370557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3186148830430092953285941 298701452852821214370557)
                  ·
                    rfl

theorem cell23_5235471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 5].length) (baseStart_5235471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235471 prefixEnd_5235471 := by exact prefixLift 5235471
  have htrace : WordTrace (prefixWord ++ tailWord_5235471) baseStart_5235471 baseEnd_5235471 := by
    simpa [prefixWord, tailWord_5235471, baseEnd_5235471] using wordTrace_append hprefix tailTrace_5235471
  have hstable : (prefixWord ++ tailWord_5235471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235471).length < 2 ^ (prefixWord ++ tailWord_5235471).sum := by decide
  have hdescent : baseEnd_5235471 < baseStart_5235471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235482 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2]
def baseStart_5235482 : Nat := 118140960795 + 5235482 * 2 ^ 59
def prefixEnd_5235482 : Nat := 4983230072969 + 3 ^ 40 * 5235482 * 2
def baseEnd_5235482 : Nat := 2688318723962590386297463

theorem tailTrace_5235482 : CollatzResearch.WordTrace tailWord_5235482 prefixEnd_5235482 2688318723962590386297463 := by
  unfold tailWord_5235482
  simp only [CollatzResearch.WordTrace]
  refine ⟨47738429004687584495965175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127302477345833558655907133 47738429004687584495965175)
  ·
    refine ⟨71607643507031376743947763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47738429004687584495965175 71607643507031376743947763)
    ·
      refine ⟨107411465260547065115921645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71607643507031376743947763 107411465260547065115921645)
      ·
        refine ⟨40279299472705149418470617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107411465260547065115921645 40279299472705149418470617)
        ·
          refine ⟨30209474604528862063852963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40279299472705149418470617 30209474604528862063852963)
          ·
            refine ⟨45314211906793293095779445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30209474604528862063852963 45314211906793293095779445)
            ·
              refine ⟨4248207366261871227729323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45314211906793293095779445 4248207366261871227729323)
              ·
                refine ⟨6372311049392806841593985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248207366261871227729323 6372311049392806841593985)
                ·
                  refine ⟨4779233287044605131195489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6372311049392806841593985 4779233287044605131195489)
                  ·
                    refine ⟨3584424965283453848396617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779233287044605131195489 3584424965283453848396617)
                    ·
                      refine ⟨2688318723962590386297463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584424965283453848396617 2688318723962590386297463)
                      ·
                        rfl

theorem cell23_5235482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_5235482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235482 prefixEnd_5235482 := by exact prefixLift 5235482
  have htrace : WordTrace (prefixWord ++ tailWord_5235482) baseStart_5235482 baseEnd_5235482 := by
    simpa [prefixWord, tailWord_5235482, baseEnd_5235482] using wordTrace_append hprefix tailTrace_5235482
  have hstable : (prefixWord ++ tailWord_5235482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235482).length < 2 ^ (prefixWord ++ tailWord_5235482).sum := by decide
  have hdescent : baseEnd_5235482 < baseStart_5235482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235533 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_5235533 : Nat := 118140960795 + 5235533 * 2 ^ 59
def prefixEnd_5235533 : Nat := 4983230072969 + 3 ^ 40 * 5235533 * 2
def baseEnd_5235533 : Nat := 2688344911475969686759729

theorem tailTrace_5235533 : CollatzResearch.WordTrace tailWord_5235533 prefixEnd_5235533 2688344911475969686759729 := by
  unfold tailWord_5235533
  simp only [CollatzResearch.WordTrace]
  refine ⟨190955576141565573693967253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127303717427710382462644835 190955576141565573693967253)
  ·
    refine ⟨8951042631635886266904715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 190955576141565573693967253 8951042631635886266904715)
    ·
      refine ⟨13426563947453829400357073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8951042631635886266904715 13426563947453829400357073)
      ·
        refine ⟨10069922960590372050267805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13426563947453829400357073 10069922960590372050267805)
        ·
          refine ⟨3776221110221389518850427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10069922960590372050267805 3776221110221389518850427)
          ·
            refine ⟨5664331665332084278275641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776221110221389518850427 5664331665332084278275641)
            ·
              refine ⟨4248248748999063208706731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5664331665332084278275641 4248248748999063208706731)
              ·
                refine ⟨6372373123498594813060097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248248748999063208706731 6372373123498594813060097)
                ·
                  refine ⟨4779279842623946109795073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6372373123498594813060097 4779279842623946109795073)
                  ·
                    refine ⟨3584459881967959582346305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779279842623946109795073 3584459881967959582346305)
                    ·
                      refine ⟨2688344911475969686759729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584459881967959582346305 2688344911475969686759729)
                      ·
                        rfl

theorem cell23_5235533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_5235533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235533 prefixEnd_5235533 := by exact prefixLift 5235533
  have htrace : WordTrace (prefixWord ++ tailWord_5235533) baseStart_5235533 baseEnd_5235533 := by
    simpa [prefixWord, tailWord_5235533, baseEnd_5235533] using wordTrace_append hprefix tailTrace_5235533
  have hstable : (prefixWord ++ tailWord_5235533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235533).length < 2 ^ (prefixWord ++ tailWord_5235533).sum := by decide
  have hdescent : baseEnd_5235533 < baseStart_5235533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235538 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_5235538 : Nat := 118140960795 + 5235538 * 2 ^ 59
def prefixEnd_5235538 : Nat := 4983230072969 + 3 ^ 40 * 5235538 * 2
def baseEnd_5235538 : Nat := 2688347478879242167197205

theorem tailTrace_5235538 : CollatzResearch.WordTrace tailWord_5235538 prefixEnd_5235538 2688347478879242167197205 := by
  unfold tailWord_5235538
  simp only [CollatzResearch.WordTrace]
  refine ⟨47738939626636864886974817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127303839004364973031932845 47738939626636864886974817)
  ·
    refine ⟨35804204719977648665231113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47738939626636864886974817 35804204719977648665231113)
    ·
      refine ⟨26853153539983236498923335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35804204719977648665231113 26853153539983236498923335)
      ·
        refine ⟨40279730309974854748385003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26853153539983236498923335 40279730309974854748385003)
        ·
          refine ⟨60419595464962282122577505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40279730309974854748385003 60419595464962282122577505)
          ·
            refine ⟨45314696598721711591933129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60419595464962282122577505 45314696598721711591933129)
            ·
              refine ⟨33986022449041283693949847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45314696598721711591933129 33986022449041283693949847)
              ·
                refine ⟨50979033673561925540924771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33986022449041283693949847 50979033673561925540924771)
                ·
                  refine ⟨76468550510342888311387157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50979033673561925540924771 76468550510342888311387157)
                  ·
                    refine ⟨3584463305172322889596273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76468550510342888311387157 3584463305172322889596273)
                    ·
                      refine ⟨2688347478879242167197205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584463305172322889596273 2688347478879242167197205)
                      ·
                        rfl

theorem cell23_5235538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_5235538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235538 prefixEnd_5235538 := by exact prefixLift 5235538
  have htrace : WordTrace (prefixWord ++ tailWord_5235538) baseStart_5235538 baseEnd_5235538 := by
    simpa [prefixWord, tailWord_5235538, baseEnd_5235538] using wordTrace_append hprefix tailTrace_5235538
  have hstable : (prefixWord ++ tailWord_5235538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235538).length < 2 ^ (prefixWord ++ tailWord_5235538).sum := by decide
  have hdescent : baseEnd_5235538 < baseStart_5235538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235565 : List Nat := [1, 5, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_5235565 : Nat := 118140960795 + 5235565 * 2 ^ 59
def prefixEnd_5235565 : Nat := 4983230072969 + 3 ^ 40 * 5235565 * 2
def baseEnd_5235565 : Nat := 896120447618971187186527

theorem tailTrace_5235565 : CollatzResearch.WordTrace tailWord_5235565 prefixEnd_5235565 896120447618971187186527 := by
  unfold tailWord_5235565
  simp only [CollatzResearch.WordTrace]
  refine ⟨190956743277449643159132149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127304495518299762106088099 190956743277449643159132149)
  ·
    refine ⟨17902194682260904046168639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190956743277449643159132149 17902194682260904046168639)
    ·
      refine ⟨26853292023391356069252959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17902194682260904046168639 26853292023391356069252959)
      ·
        refine ⟨40279938035087034103879439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26853292023391356069252959 40279938035087034103879439)
        ·
          refine ⟨60419907052630551155819159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40279938035087034103879439 60419907052630551155819159)
          ·
            refine ⟨90629860578945826733728739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60419907052630551155819159 90629860578945826733728739)
            ·
              refine ⟨135944790868418740100593109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90629860578945826733728739 135944790868418740100593109)
              ·
                refine ⟨3186206035978564221107651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135944790868418740100593109 3186206035978564221107651)
                ·
                  refine ⟨4779309053967846331661477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186206035978564221107651 4779309053967846331661477)
                  ·
                    refine ⟨896120447618971187186527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4779309053967846331661477 896120447618971187186527)
                    ·
                      rfl

theorem cell23_5235565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_5235565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235565 prefixEnd_5235565 := by exact prefixLift 5235565
  have htrace : WordTrace (prefixWord ++ tailWord_5235565) baseStart_5235565 baseEnd_5235565 := by
    simpa [prefixWord, tailWord_5235565, baseEnd_5235565] using wordTrace_append hprefix tailTrace_5235565
  have hstable : (prefixWord ++ tailWord_5235565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235565).length < 2 ^ (prefixWord ++ tailWord_5235565).sum := by decide
  have hdescent : baseEnd_5235565 < baseStart_5235565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235605 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_5235605 : Nat := 118140960795 + 5235605 * 2 ^ 59
def prefixEnd_5235605 : Nat := 4983230072969 + 3 ^ 40 * 5235605 * 2
def baseEnd_5235605 : Nat := 2688381882083093405059397

theorem tailTrace_5235605 : CollatzResearch.WordTrace tailWord_5235605 prefixEnd_5235605 2688381882083093405059397 := by
  unfold tailWord_5235605
  simp only [CollatzResearch.WordTrace]
  refine ⟨190958202197304729990588269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127305468131536486660392179 190958202197304729990588269)
  ·
    refine ⟨71609325823989273746470601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190958202197304729990588269 71609325823989273746470601)
    ·
      refine ⟨53706994367991955309852951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71609325823989273746470601 53706994367991955309852951)
      ·
        refine ⟨80560491551987932964779427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53706994367991955309852951 80560491551987932964779427)
        ·
          refine ⟨120840737327981899447169141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80560491551987932964779427 120840737327981899447169141)
          ·
            refine ⟨11328819124498303073172107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120840737327981899447169141 11328819124498303073172107)
            ·
              refine ⟨16993228686747454609758161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11328819124498303073172107 16993228686747454609758161)
              ·
                refine ⟨12744921515060590957318621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16993228686747454609758161 12744921515060590957318621)
                ·
                  refine ⟨4779345568147721608994483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12744921515060590957318621 4779345568147721608994483)
                  ·
                    refine ⟨7169018352221582413491725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4779345568147721608994483 7169018352221582413491725)
                    ·
                      refine ⟨2688381882083093405059397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7169018352221582413491725 2688381882083093405059397)
                      ·
                        rfl

theorem cell23_5235605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_5235605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235605 prefixEnd_5235605 := by exact prefixLift 5235605
  have htrace : WordTrace (prefixWord ++ tailWord_5235605) baseStart_5235605 baseEnd_5235605 := by
    simpa [prefixWord, tailWord_5235605, baseEnd_5235605] using wordTrace_append hprefix tailTrace_5235605
  have hstable : (prefixWord ++ tailWord_5235605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235605).length < 2 ^ (prefixWord ++ tailWord_5235605).sum := by decide
  have hdescent : baseEnd_5235605 < baseStart_5235605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235615 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 1, 5, 2]
def baseStart_5235615 : Nat := 118140960795 + 5235615 * 2 ^ 59
def prefixEnd_5235615 : Nat := 4983230072969 + 3 ^ 40 * 5235615 * 2
def baseEnd_5235615 : Nat := 2688387016889638365934351

theorem tailTrace_5235615 : CollatzResearch.WordTrace tailWord_5235615 prefixEnd_5235615 2688387016889638365934351 := by
  unfold tailWord_5235615
  simp only [CollatzResearch.WordTrace]
  refine ⟨190958566927268501698452299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127305711284845667798968199 190958566927268501698452299)
  ·
    refine ⟨286437850390902752547678449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190958566927268501698452299 286437850390902752547678449)
    ·
      refine ⟨214828387793177064410758837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286437850390902752547678449 214828387793177064410758837)
      ·
        refine ⟨20140161355610349788508641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214828387793177064410758837 20140161355610349788508641)
        ·
          refine ⟨15105121016707762341381481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20140161355610349788508641 15105121016707762341381481)
          ·
            refine ⟨11328840762530821756036111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15105121016707762341381481 11328840762530821756036111)
            ·
              refine ⟨16993261143796232634054167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11328840762530821756036111 16993261143796232634054167)
              ·
                refine ⟨25489891715694348951081251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16993261143796232634054167 25489891715694348951081251)
                ·
                  refine ⟨38234837573541523426621877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25489891715694348951081251 38234837573541523426621877)
                  ·
                    refine ⟨3584516022519517821245801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38234837573541523426621877 3584516022519517821245801)
                    ·
                      refine ⟨2688387016889638365934351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584516022519517821245801 2688387016889638365934351)
                      ·
                        rfl

theorem cell23_5235615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_5235615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235615 prefixEnd_5235615 := by exact prefixLift 5235615
  have htrace : WordTrace (prefixWord ++ tailWord_5235615) baseStart_5235615 baseEnd_5235615 := by
    simpa [prefixWord, tailWord_5235615, baseEnd_5235615] using wordTrace_append hprefix tailTrace_5235615
  have hstable : (prefixWord ++ tailWord_5235615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235615).length < 2 ^ (prefixWord ++ tailWord_5235615).sum := by decide
  have hdescent : baseEnd_5235615 < baseStart_5235615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235628 : List Nat := [2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 4]
def baseStart_5235628 : Nat := 118140960795 + 5235628 * 2 ^ 59
def prefixEnd_5235628 : Nat := 4983230072969 + 3 ^ 40 * 5235628 * 2
def baseEnd_5235628 : Nat := 2688393692138146815071791

theorem tailTrace_5235628 : CollatzResearch.WordTrace tailWord_5235628 prefixEnd_5235628 2688393692138146815071791 := by
  unfold tailWord_5235628
  simp only [CollatzResearch.WordTrace]
  refine ⟨95479520538110702459337769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127306027384147603279117025 95479520538110702459337769)
  ·
    refine ⟨71609640403583026844503327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95479520538110702459337769 71609640403583026844503327)
    ·
      refine ⟨107414460605374540266754991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71609640403583026844503327 107414460605374540266754991)
      ·
        refine ⟨161121690908061810400132487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107414460605374540266754991 161121690908061810400132487)
        ·
          refine ⟨241682536362092715600198731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161121690908061810400132487 241682536362092715600198731)
          ·
            refine ⟨362523804543139073400298097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241682536362092715600198731 362523804543139073400298097)
            ·
              refine ⟨271892853407354305050223573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362523804543139073400298097 271892853407354305050223573)
              ·
                refine ⟨6372488751734866524614615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 271892853407354305050223573 6372488751734866524614615)
                ·
                  refine ⟨9558733127602299786921923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6372488751734866524614615 9558733127602299786921923)
                  ·
                    refine ⟨14338099691403449680382885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9558733127602299786921923 14338099691403449680382885)
                    ·
                      refine ⟨2688393692138146815071791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14338099691403449680382885 2688393692138146815071791)
                      ·
                        rfl

theorem cell23_5235628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_5235628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235628 prefixEnd_5235628 := by exact prefixLift 5235628
  have htrace : WordTrace (prefixWord ++ tailWord_5235628) baseStart_5235628 baseEnd_5235628 := by
    simpa [prefixWord, tailWord_5235628, baseEnd_5235628] using wordTrace_append hprefix tailTrace_5235628
  have hstable : (prefixWord ++ tailWord_5235628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235628).length < 2 ^ (prefixWord ++ tailWord_5235628).sum := by decide
  have hdescent : baseEnd_5235628 < baseStart_5235628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235629 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 6]
def baseStart_5235629 : Nat := 118140960795 + 5235629 * 2 ^ 59
def prefixEnd_5235629 : Nat := 4983230072969 + 3 ^ 40 * 5235629 * 2
def baseEnd_5235629 : Nat := 298710467290977923462143

theorem tailTrace_5235629 : CollatzResearch.WordTrace tailWord_5235629 prefixEnd_5235629 298710467290977923462143 := by
  unfold tailWord_5235629
  simp only [CollatzResearch.WordTrace]
  refine ⟨190959077549217782089461941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127306051699478521392974627 190959077549217782089461941)
  ·
    refine ⟨17902413520239167070887057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190959077549217782089461941 17902413520239167070887057)
    ·
      refine ⟨13426810140179375303165293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17902413520239167070887057 13426810140179375303165293)
      ·
        refine ⟨5035053802567265738686985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13426810140179375303165293 5035053802567265738686985)
        ·
          refine ⟨3776290351925449304015239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5035053802567265738686985 3776290351925449304015239)
          ·
            refine ⟨5664435527888173956022859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776290351925449304015239 5664435527888173956022859)
            ·
              refine ⟨8496653291832260934034289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664435527888173956022859 8496653291832260934034289)
              ·
                refine ⟨6372489968874195700525717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8496653291832260934034289 6372489968874195700525717)
                ·
                  refine ⟨298710467290977923462143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6372489968874195700525717 298710467290977923462143)
                  ·
                    rfl

theorem cell23_5235629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_5235629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235629 prefixEnd_5235629 := by exact prefixLift 5235629
  have htrace : WordTrace (prefixWord ++ tailWord_5235629) baseStart_5235629 baseEnd_5235629 := by
    simpa [prefixWord, tailWord_5235629, baseEnd_5235629] using wordTrace_append hprefix tailTrace_5235629
  have hstable : (prefixWord ++ tailWord_5235629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235629).length < 2 ^ (prefixWord ++ tailWord_5235629).sum := by decide
  have hdescent : baseEnd_5235629 < baseStart_5235629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235648 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_5235648 : Nat := 118140960795 + 5235648 * 2 ^ 59
def prefixEnd_5235648 : Nat := 4983230072969 + 3 ^ 40 * 5235648 * 2
def baseEnd_5235648 : Nat := 2688403961751236736821699

theorem tailTrace_5235648 : CollatzResearch.WordTrace tailWord_5235648 prefixEnd_5235648 2688403961751236736821699 := by
  unfold tailWord_5235648
  simp only [CollatzResearch.WordTrace]
  refine ⟨95479885268074474167201799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127306513690765965556269065 95479885268074474167201799)
  ·
    refine ⟨143219827902111711250802699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95479885268074474167201799 143219827902111711250802699)
    ·
      refine ⟨214829741853167566876204049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143219827902111711250802699 214829741853167566876204049)
      ·
        refine ⟨161122306389875675157153037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214829741853167566876204049 161122306389875675157153037)
        ·
          refine ⟨60420864896203378183932389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161122306389875675157153037 60420864896203378183932389)
          ·
            refine ⟨11328912168038133409487323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60420864896203378183932389 11328912168038133409487323)
            ·
              refine ⟨16993368252057200114230985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11328912168038133409487323 16993368252057200114230985)
              ·
                refine ⟨12745026189042900085673239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16993368252057200114230985 12745026189042900085673239)
                ·
                  refine ⟨19117539283564350128509859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12745026189042900085673239 19117539283564350128509859)
                  ·
                    refine ⟨28676308925346525192764789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19117539283564350128509859 28676308925346525192764789)
                    ·
                      refine ⟨2688403961751236736821699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28676308925346525192764789 2688403961751236736821699)
                      ·
                        rfl

theorem cell23_5235648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_5235648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235648 prefixEnd_5235648 := by exact prefixLift 5235648
  have htrace : WordTrace (prefixWord ++ tailWord_5235648) baseStart_5235648 baseEnd_5235648 := by
    simpa [prefixWord, tailWord_5235648, baseEnd_5235648] using wordTrace_append hprefix tailTrace_5235648
  have hstable : (prefixWord ++ tailWord_5235648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235648).length < 2 ^ (prefixWord ++ tailWord_5235648).sum := by decide
  have hdescent : baseEnd_5235648 < baseStart_5235648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235662 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_5235662 : Nat := 118140960795 + 5235662 * 2 ^ 59
def prefixEnd_5235662 : Nat := 4983230072969 + 3 ^ 40 * 5235662 * 2
def baseEnd_5235662 : Nat := 2688411150480399682046635

theorem tailTrace_5235662 : CollatzResearch.WordTrace tailWord_5235662 prefixEnd_5235662 2688411150480399682046635 := by
  unfold tailWord_5235662
  simp only [CollatzResearch.WordTrace]
  refine ⟨23870035144762278590676655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127306854105398819150275493 23870035144762278590676655)
  ·
    refine ⟨35805052717143417886014983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23870035144762278590676655 35805052717143417886014983)
    ·
      refine ⟨53707579075715126829022475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35805052717143417886014983 53707579075715126829022475)
      ·
        refine ⟨80561368613572690243533713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53707579075715126829022475 80561368613572690243533713)
        ·
          refine ⟨60421026460179517682650285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80561368613572690243533713 60421026460179517682650285)
          ·
            refine ⟨22657884922567319130993857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60421026460179517682650285 22657884922567319130993857)
            ·
              refine ⟨16993413691925489348245393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22657884922567319130993857 16993413691925489348245393)
              ·
                refine ⟨12745060268944117011184045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16993413691925489348245393 12745060268944117011184045)
                ·
                  refine ⟨4779397600854043879194017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12745060268944117011184045 4779397600854043879194017)
                  ·
                    refine ⟨3584548200640532909395513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779397600854043879194017 3584548200640532909395513)
                    ·
                      refine ⟨2688411150480399682046635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584548200640532909395513 2688411150480399682046635)
                      ·
                        rfl

theorem cell23_5235662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_5235662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235662 prefixEnd_5235662 := by exact prefixLift 5235662
  have htrace : WordTrace (prefixWord ++ tailWord_5235662) baseStart_5235662 baseEnd_5235662 := by
    simpa [prefixWord, tailWord_5235662, baseEnd_5235662] using wordTrace_append hprefix tailTrace_5235662
  have hstable : (prefixWord ++ tailWord_5235662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235662).length < 2 ^ (prefixWord ++ tailWord_5235662).sum := by decide
  have hdescent : baseEnd_5235662 < baseStart_5235662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235665 : List Nat := [1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 3]
def baseStart_5235665 : Nat := 118140960795 + 5235665 * 2 ^ 59
def prefixEnd_5235665 : Nat := 4983230072969 + 3 ^ 40 * 5235665 * 2
def baseEnd_5235665 : Nat := 2688412690922363170309121

theorem tailTrace_5235665 : CollatzResearch.WordTrace tailWord_5235665 prefixEnd_5235665 2688412690922363170309121 := by
  unfold tailWord_5235665
  simp only [CollatzResearch.WordTrace]
  refine ⟨190960390577087360237772449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127306927051391573491848299 190960390577087360237772449)
  ·
    refine ⟨143220292932815520178329337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190960390577087360237772449 143220292932815520178329337)
    ·
      refine ⟨107415219699611640133747003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143220292932815520178329337 107415219699611640133747003)
      ·
        refine ⟨161122829549417460200620505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107415219699611640133747003 161122829549417460200620505)
        ·
          refine ⟨120842122162063095150465379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161122829549417460200620505 120842122162063095150465379)
          ·
            refine ⟨181263183243094642725698069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120842122162063095150465379 181263183243094642725698069)
            ·
              refine ⟨8496711714520061377767097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 181263183243094642725698069 8496711714520061377767097)
              ·
                refine ⟨6372533785890046033325323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8496711714520061377767097 6372533785890046033325323)
                ·
                  refine ⟨9558800678835069049987985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6372533785890046033325323 9558800678835069049987985)
                  ·
                    refine ⟨7169100509126301787490989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9558800678835069049987985 7169100509126301787490989)
                    ·
                      refine ⟨2688412690922363170309121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7169100509126301787490989 2688412690922363170309121)
                      ·
                        rfl

theorem cell23_5235665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_5235665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235665 prefixEnd_5235665 := by exact prefixLift 5235665
  have htrace : WordTrace (prefixWord ++ tailWord_5235665) baseStart_5235665 baseEnd_5235665 := by
    simpa [prefixWord, tailWord_5235665, baseEnd_5235665] using wordTrace_append hprefix tailTrace_5235665
  have hstable : (prefixWord ++ tailWord_5235665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235665).length < 2 ^ (prefixWord ++ tailWord_5235665).sum := by decide
  have hdescent : baseEnd_5235665 < baseStart_5235665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235668 : List Nat := [2, 4, 1, 2, 1, 3, 1, 9]
def baseStart_5235668 : Nat := 118140960795 + 5235668 * 2 ^ 59
def prefixEnd_5235668 : Nat := 4983230072969 + 3 ^ 40 * 5235668 * 2
def baseEnd_5235668 : Nat := 99570897457938024391541

theorem tailTrace_5235668 : CollatzResearch.WordTrace tailWord_5235668 prefixEnd_5235668 99570897457938024391541 := by
  unfold tailWord_5235668
  simp only [CollatzResearch.WordTrace]
  refine ⟨95480249998038245875065829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127306999997384327833421105 95480249998038245875065829)
  ·
    refine ⟨17902546874632171101574843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95480249998038245875065829 17902546874632171101574843)
    ·
      refine ⟨26853820311948256652362265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17902546874632171101574843 26853820311948256652362265)
      ·
        refine ⟨20140365233961192489271699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26853820311948256652362265 20140365233961192489271699)
        ·
          refine ⟨30210547850941788733907549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20140365233961192489271699 30210547850941788733907549)
          ·
            refine ⟨11328955444103170775215331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30210547850941788733907549 11328955444103170775215331)
            ·
              refine ⟨16993433166154756162822997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11328955444103170775215331 16993433166154756162822997)
              ·
                refine ⟨99570897457938024391541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16993433166154756162822997 99570897457938024391541)
                ·
                  rfl

theorem cell23_5235668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 9].length) (baseStart_5235668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235668 prefixEnd_5235668 := by exact prefixLift 5235668
  have htrace : WordTrace (prefixWord ++ tailWord_5235668) baseStart_5235668 baseEnd_5235668 := by
    simpa [prefixWord, tailWord_5235668, baseEnd_5235668] using wordTrace_append hprefix tailTrace_5235668
  have hstable : (prefixWord ++ tailWord_5235668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235668).length < 2 ^ (prefixWord ++ tailWord_5235668).sum := by decide
  have hdescent : baseEnd_5235668 < baseStart_5235668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235681 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 1, 9]
def baseStart_5235681 : Nat := 118140960795 + 5235681 * 2 ^ 59
def prefixEnd_5235681 : Nat := 4983230072969 + 3 ^ 40 * 5235681 * 2
def baseEnd_5235681 : Nat := 896140302204278369236349

theorem tailTrace_5235681 : CollatzResearch.WordTrace tailWord_5235681 prefixEnd_5235681 896140302204278369236349 := by
  unfold tailWord_5235681
  simp only [CollatzResearch.WordTrace]
  refine ⟨190960974145029394970354897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127307316096686263313569931 190960974145029394970354897)
  ·
    refine ⟨143220730608772046227766173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190960974145029394970354897 143220730608772046227766173)
    ·
      refine ⟨53707773978289517335412315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143220730608772046227766173 53707773978289517335412315)
      ·
        refine ⟨80561660967434276003118473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53707773978289517335412315 80561660967434276003118473)
        ·
          refine ⟨60421245725575707002338855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80561660967434276003118473 60421245725575707002338855)
          ·
            refine ⟨90631868588363560503508283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60421245725575707002338855 90631868588363560503508283)
            ·
              refine ⟨135947802882545340755262425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90631868588363560503508283 135947802882545340755262425)
              ·
                refine ⟨101960852161909005566446819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135947802882545340755262425 101960852161909005566446819)
                ·
                  refine ⟨152941278242863508349670229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101960852161909005566446819 152941278242863508349670229)
                  ·
                    refine ⟨896140302204278369236349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 152941278242863508349670229 896140302204278369236349)
                    ·
                      rfl

theorem cell23_5235681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_5235681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235681 prefixEnd_5235681 := by exact prefixLift 5235681
  have htrace : WordTrace (prefixWord ++ tailWord_5235681) baseStart_5235681 baseEnd_5235681 := by
    simpa [prefixWord, tailWord_5235681, baseEnd_5235681] using wordTrace_append hprefix tailTrace_5235681
  have hstable : (prefixWord ++ tailWord_5235681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235681).length < 2 ^ (prefixWord ++ tailWord_5235681).sum := by decide
  have hdescent : baseEnd_5235681 < baseStart_5235681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235682 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5235682 : Nat := 118140960795 + 5235682 * 2 ^ 59
def prefixEnd_5235682 : Nat := 4983230072969 + 3 ^ 40 * 5235682 * 2
def baseEnd_5235682 : Nat := 2688421420093489603796543

theorem tailTrace_5235682 : CollatzResearch.WordTrace tailWord_5235682 prefixEnd_5235682 2688421420093489603796543 := by
  unfold tailWord_5235682
  simp only [CollatzResearch.WordTrace]
  refine ⟨47740252654506443035285325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127307340412017181427427533 47740252654506443035285325)
  ·
    refine ⟨17902594745439916138231997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47740252654506443035285325 17902594745439916138231997)
    ·
      refine ⟨6713473029539968551836999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17902594745439916138231997 6713473029539968551836999)
      ·
        refine ⟨10070209544309952827755499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6713473029539968551836999 10070209544309952827755499)
        ·
          refine ⟨15105314316464929241633249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10070209544309952827755499 15105314316464929241633249)
          ·
            refine ⟨11328985737348696931224937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15105314316464929241633249 11328985737348696931224937)
            ·
              refine ⟨8496739303011522698418703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11328985737348696931224937 8496739303011522698418703)
              ·
                refine ⟨12745108954517284047628055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8496739303011522698418703 12745108954517284047628055)
                ·
                  refine ⟨19117663431775926071442083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12745108954517284047628055 19117663431775926071442083)
                  ·
                    refine ⟨28676495147663889107163125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19117663431775926071442083 28676495147663889107163125)
                    ·
                      refine ⟨2688421420093489603796543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28676495147663889107163125 2688421420093489603796543)
                      ·
                        rfl

theorem cell23_5235682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5235682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235682 prefixEnd_5235682 := by exact prefixLift 5235682
  have htrace : WordTrace (prefixWord ++ tailWord_5235682) baseStart_5235682 baseEnd_5235682 := by
    simpa [prefixWord, tailWord_5235682, baseEnd_5235682] using wordTrace_append hprefix tailTrace_5235682
  have hstable : (prefixWord ++ tailWord_5235682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235682).length < 2 ^ (prefixWord ++ tailWord_5235682).sum := by decide
  have hdescent : baseEnd_5235682 < baseStart_5235682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235685 : List Nat := [1, 3, 1, 6, 1, 2, 9]
def baseStart_5235685 : Nat := 118140960795 + 5235685 * 2 ^ 59
def prefixEnd_5235685 : Nat := 4983230072969 + 3 ^ 40 * 5235685 * 2
def baseEnd_5235685 : Nat := 33190406920190778914309

theorem tailTrace_5235685 : CollatzResearch.WordTrace tailWord_5235685 prefixEnd_5235685 33190406920190778914309 := by
  unfold tailWord_5235685
  simp only [CollatzResearch.WordTrace]
  refine ⟨190961120037014903653500509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127307413358009935769000339 190961120037014903653500509)
  ·
    refine ⟨71610420013880588870062691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190961120037014903653500509 71610420013880588870062691)
    ·
      refine ⟨107415630020820883305094037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71610420013880588870062691 107415630020820883305094037)
      ·
        refine ⟨5035107657225978904926283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 107415630020820883305094037 5035107657225978904926283)
        ·
          refine ⟨7552661485838968357389425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035107657225978904926283 7552661485838968357389425)
          ·
            refine ⟨5664496114379226268042069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7552661485838968357389425 5664496114379226268042069)
            ·
              refine ⟨33190406920190778914309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5664496114379226268042069 33190406920190778914309)
              ·
                rfl

theorem cell23_5235685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 9].length) (baseStart_5235685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235685 prefixEnd_5235685 := by exact prefixLift 5235685
  have htrace : WordTrace (prefixWord ++ tailWord_5235685) baseStart_5235685 baseEnd_5235685 := by
    simpa [prefixWord, tailWord_5235685, baseEnd_5235685] using wordTrace_append hprefix tailTrace_5235685
  have hstable : (prefixWord ++ tailWord_5235685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235685).length < 2 ^ (prefixWord ++ tailWord_5235685).sum := by decide
  have hdescent : baseEnd_5235685 < baseStart_5235685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235695 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 3]
def baseStart_5235695 : Nat := 118140960795 + 5235695 * 2 ^ 59
def prefixEnd_5235695 : Nat := 4983230072969 + 3 ^ 40 * 5235695 * 2
def baseEnd_5235695 : Nat := 2688428095341998052933983

theorem tailTrace_5235695 : CollatzResearch.WordTrace tailWord_5235695 prefixEnd_5235695 2688428095341998052933983 := by
  unfold tailWord_5235695
  simp only [CollatzResearch.WordTrace]
  refine ⟨190961484766978675361364539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127307656511319116907576359 190961484766978675361364539)
  ·
    refine ⟨286442227150468013042046809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190961484766978675361364539 286442227150468013042046809)
    ·
      refine ⟨214831670362851009781535107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286442227150468013042046809 214831670362851009781535107)
      ·
        refine ⟨322247505544276514672302661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214831670362851009781535107 322247505544276514672302661)
        ·
          refine ⟨60421407289551846501056749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 322247505544276514672302661 60421407289551846501056749)
          ·
            refine ⟨22658027733581942437896281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60421407289551846501056749 22658027733581942437896281)
            ·
              refine ⟨16993520800186456828422211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22658027733581942437896281 16993520800186456828422211)
              ·
                refine ⟨25490281200279685242633317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16993520800186456828422211 25490281200279685242633317)
                ·
                  refine ⟨4779427725052440982993747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25490281200279685242633317 4779427725052440982993747)
                  ·
                    refine ⟨7169141587578661474490621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4779427725052440982993747 7169141587578661474490621)
                    ·
                      refine ⟨2688428095341998052933983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7169141587578661474490621 2688428095341998052933983)
                      ·
                        rfl

theorem cell23_5235695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 3].length) (baseStart_5235695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235695 prefixEnd_5235695 := by exact prefixLift 5235695
  have htrace : WordTrace (prefixWord ++ tailWord_5235695) baseStart_5235695 baseEnd_5235695 := by
    simpa [prefixWord, tailWord_5235695, baseEnd_5235695] using wordTrace_append hprefix tailTrace_5235695
  have hstable : (prefixWord ++ tailWord_5235695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235695).length < 2 ^ (prefixWord ++ tailWord_5235695).sum := by decide
  have hdescent : baseEnd_5235695 < baseStart_5235695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235705 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 3, 3, 2]
def baseStart_5235705 : Nat := 118140960795 + 5235705 * 2 ^ 59
def prefixEnd_5235705 : Nat := 4983230072969 + 3 ^ 40 * 5235705 * 2
def baseEnd_5235705 : Nat := 2688433230148543013808937

theorem tailTrace_5235705 : CollatzResearch.WordTrace tailWord_5235705 prefixEnd_5235705 2688433230148543013808937 := by
  unfold tailWord_5235705
  simp only [CollatzResearch.WordTrace]
  refine ⟨190961849496942447069228569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127307899664628298046152379 190961849496942447069228569)
  ·
    refine ⟨143221387122706835301921427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190961849496942447069228569 143221387122706835301921427)
    ·
      refine ⟨214832080684060252952882141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143221387122706835301921427 214832080684060252952882141)
      ·
        refine ⟨80562030256522594857330803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214832080684060252952882141 80562030256522594857330803)
        ·
          refine ⟨120843045384783892285996205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80562030256522594857330803 120843045384783892285996205)
          ·
            refine ⟨45316142019293959607248577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120843045384783892285996205 45316142019293959607248577)
            ·
              refine ⟨33987106514470469705436433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45316142019293959607248577 33987106514470469705436433)
              ·
                refine ⟨25490329885852852279077325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33987106514470469705436433 25490329885852852279077325)
                ·
                  refine ⟨9558873707194819604653997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25490329885852852279077325 9558873707194819604653997)
                  ·
                    refine ⟨3584577640198057351745249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9558873707194819604653997 3584577640198057351745249)
                    ·
                      refine ⟨2688433230148543013808937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584577640198057351745249 2688433230148543013808937)
                      ·
                        rfl

theorem cell23_5235705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_5235705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235705 prefixEnd_5235705 := by exact prefixLift 5235705
  have htrace : WordTrace (prefixWord ++ tailWord_5235705) baseStart_5235705 baseEnd_5235705 := by
    simpa [prefixWord, tailWord_5235705, baseEnd_5235705] using wordTrace_append hprefix tailTrace_5235705
  have hstable : (prefixWord ++ tailWord_5235705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235705).length < 2 ^ (prefixWord ++ tailWord_5235705).sum := by decide
  have hdescent : baseEnd_5235705 < baseStart_5235705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235722 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_5235722 : Nat := 118140960795 + 5235722 * 2 ^ 59
def prefixEnd_5235722 : Nat := 4983230072969 + 3 ^ 40 * 5235722 * 2
def baseEnd_5235722 : Nat := 2688441959319669447296359

theorem tailTrace_5235722 : CollatzResearch.WordTrace tailWord_5235722 prefixEnd_5235722 2688441959319669447296359 := by
  unfold tailWord_5235722
  simp only [CollatzResearch.WordTrace]
  refine ⟨47740617384470214743149355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127308313025253905981731613 47740617384470214743149355)
  ·
    refine ⟨71610926076705322114724033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47740617384470214743149355 71610926076705322114724033)
    ·
      refine ⟨53708194557528991586043025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71610926076705322114724033 53708194557528991586043025)
      ·
        refine ⟨40281145918146743689532269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53708194557528991586043025 40281145918146743689532269)
        ·
          refine ⟨15105429719305028883574601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40281145918146743689532269 15105429719305028883574601)
          ·
            refine ⟨11329072289478771662680951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15105429719305028883574601 11329072289478771662680951)
            ·
              refine ⟨16993608434218157494021427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11329072289478771662680951 16993608434218157494021427)
              ·
                refine ⟨25490412651327236241032141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16993608434218157494021427 25490412651327236241032141)
                ·
                  refine ⟨9558904744247713590387053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25490412651327236241032141 9558904744247713590387053)
                  ·
                    refine ⟨3584589279092892596395145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9558904744247713590387053 3584589279092892596395145)
                    ·
                      refine ⟨2688441959319669447296359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584589279092892596395145 2688441959319669447296359)
                      ·
                        rfl

theorem cell23_5235722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_5235722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235722 prefixEnd_5235722 := by exact prefixLift 5235722
  have htrace : WordTrace (prefixWord ++ tailWord_5235722) baseStart_5235722 baseEnd_5235722 := by
    simpa [prefixWord, tailWord_5235722, baseEnd_5235722] using wordTrace_append hprefix tailTrace_5235722
  have hstable : (prefixWord ++ tailWord_5235722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235722).length < 2 ^ (prefixWord ++ tailWord_5235722).sum := by decide
  have hdescent : baseEnd_5235722 < baseStart_5235722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235738 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_5235738 : Nat := 118140960795 + 5235738 * 2 ^ 59
def prefixEnd_5235738 : Nat := 4983230072969 + 3 ^ 40 * 5235738 * 2
def baseEnd_5235738 : Nat := 2688450175010141384696285

theorem tailTrace_5235738 : CollatzResearch.WordTrace tailWord_5235738 prefixEnd_5235738 2688450175010141384696285 := by
  unfold tailWord_5235738
  simp only [CollatzResearch.WordTrace]
  refine ⟨47740763276455723426294967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127308702070548595803453245 47740763276455723426294967)
  ·
    refine ⟨71611144914683585139442451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47740763276455723426294967 71611144914683585139442451)
    ·
      refine ⟨107416717372025377709163677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71611144914683585139442451 107416717372025377709163677)
      ·
        refine ⟨40281269014509516640936379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107416717372025377709163677 40281269014509516640936379)
        ·
          refine ⟨60421903521764274961404569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40281269014509516640936379 60421903521764274961404569)
          ·
            refine ⟨45316427641323206221053427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60421903521764274961404569 45316427641323206221053427)
            ·
              refine ⟨67974641461984809331580141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45316427641323206221053427 67974641461984809331580141)
              ·
                refine ⟨25490490548244303499342553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67974641461984809331580141 25490490548244303499342553)
                ·
                  refine ⟨19117867911183227624506915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25490490548244303499342553 19117867911183227624506915)
                  ·
                    refine ⟨28676801866774841436760373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19117867911183227624506915 28676801866774841436760373)
                    ·
                      refine ⟨2688450175010141384696285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28676801866774841436760373 2688450175010141384696285)
                      ·
                        rfl

theorem cell23_5235738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_5235738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235738 prefixEnd_5235738 := by exact prefixLift 5235738
  have htrace : WordTrace (prefixWord ++ tailWord_5235738) baseStart_5235738 baseEnd_5235738 := by
    simpa [prefixWord, tailWord_5235738, baseEnd_5235738] using wordTrace_append hprefix tailTrace_5235738
  have hstable : (prefixWord ++ tailWord_5235738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235738).length < 2 ^ (prefixWord ++ tailWord_5235738).sum := by decide
  have hdescent : baseEnd_5235738 < baseStart_5235738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235769 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 2, 2, 2]
def baseStart_5235769 : Nat := 118140960795 + 5235769 * 2 ^ 59
def prefixEnd_5235769 : Nat := 4983230072969 + 3 ^ 40 * 5235769 * 2
def baseEnd_5235769 : Nat := 2688466092910430763408643

theorem tailTrace_5235769 : CollatzResearch.WordTrace tailWord_5235769 prefixEnd_5235769 2688466092910430763408643 := by
  unfold tailWord_5235769
  simp only [CollatzResearch.WordTrace]
  refine ⟨190964183768710585999558361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127309455845807057333038907 190964183768710585999558361)
  ·
    refine ⟨143223137826532939499668771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190964183768710585999558361 143223137826532939499668771)
    ·
      refine ⟨214834706739799409249503157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143223137826532939499668771 214834706739799409249503157)
      ·
        refine ⟨20140753756856194617140921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214834706739799409249503157 20140753756856194617140921)
        ·
          refine ⟨15105565317642145962855691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20140753756856194617140921 15105565317642145962855691)
          ·
            refine ⟨22658347976463218944283537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15105565317642145962855691 22658347976463218944283537)
            ·
              refine ⟨16993760982347414208212653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22658347976463218944283537 16993760982347414208212653)
              ·
                refine ⟨6372660368380280328079745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16993760982347414208212653 6372660368380280328079745)
                ·
                  refine ⟨4779495276285210246059809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6372660368380280328079745 4779495276285210246059809)
                  ·
                    refine ⟨3584621457213907684544857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779495276285210246059809 3584621457213907684544857)
                    ·
                      refine ⟨2688466092910430763408643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584621457213907684544857 2688466092910430763408643)
                      ·
                        rfl

theorem cell23_5235769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_5235769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235769 prefixEnd_5235769 := by exact prefixLift 5235769
  have htrace : WordTrace (prefixWord ++ tailWord_5235769) baseStart_5235769 baseEnd_5235769 := by
    simpa [prefixWord, tailWord_5235769, baseEnd_5235769] using wordTrace_append hprefix tailTrace_5235769
  have hstable : (prefixWord ++ tailWord_5235769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235769).length < 2 ^ (prefixWord ++ tailWord_5235769).sum := by decide
  have hdescent : baseEnd_5235769 < baseStart_5235769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235825 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 1, 6, 2]
def baseStart_5235825 : Nat := 118140960795 + 5235825 * 2 ^ 59
def prefixEnd_5235825 : Nat := 4983230072969 + 3 ^ 40 * 5235825 * 2
def baseEnd_5235825 : Nat := 2688494847827082544308385

theorem tailTrace_5235825 : CollatzResearch.WordTrace tailWord_5235825 prefixEnd_5235825 2688494847827082544308385 := by
  unfold tailWord_5235825
  simp only [CollatzResearch.WordTrace]
  refine ⟨190966226256507707563596929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127310817504338471709064619 190966226256507707563596929)
  ·
    refine ⟨143224669692380780672697697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190966226256507707563596929 143224669692380780672697697)
    ·
      refine ⟨107418502269285585504523273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143224669692380780672697697 107418502269285585504523273)
      ·
        refine ⟨80563876701964189128392455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107418502269285585504523273 80563876701964189128392455)
        ·
          refine ⟨120845815052946283692588683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80563876701964189128392455 120845815052946283692588683)
          ·
            refine ⟨181268722579419425538883025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120845815052946283692588683 181268722579419425538883025)
            ·
              refine ⟨135951541934564569154162269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181268722579419425538883025 135951541934564569154162269)
              ·
                refine ⟨50981828225461713432810851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135951541934564569154162269 50981828225461713432810851)
                ·
                  refine ⟨76472742338192570149216277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50981828225461713432810851 76472742338192570149216277)
                  ·
                    refine ⟨3584659797102776725744513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76472742338192570149216277 3584659797102776725744513)
                    ·
                      refine ⟨2688494847827082544308385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584659797102776725744513 2688494847827082544308385)
                      ·
                        rfl

theorem cell23_5235825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_5235825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235825 prefixEnd_5235825 := by exact prefixLift 5235825
  have htrace : WordTrace (prefixWord ++ tailWord_5235825) baseStart_5235825 baseEnd_5235825 := by
    simpa [prefixWord, tailWord_5235825, baseEnd_5235825] using wordTrace_append hprefix tailTrace_5235825
  have hstable : (prefixWord ++ tailWord_5235825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235825).length < 2 ^ (prefixWord ++ tailWord_5235825).sum := by decide
  have hdescent : baseEnd_5235825 < baseStart_5235825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235888 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_5235888 : Nat := 118140960795 + 5235888 * 2 ^ 59
def prefixEnd_5235888 : Nat := 4983230072969 + 3 ^ 40 * 5235888 * 2
def baseEnd_5235888 : Nat := 2688527197108315797820595

theorem tailTrace_5235888 : CollatzResearch.WordTrace tailWord_5235888 prefixEnd_5235888 2688527197108315797820595 := by
  unfold tailWord_5235888
  simp only [CollatzResearch.WordTrace]
  refine ⟨95484262027639734661570159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127312349370186312882093545 95484262027639734661570159)
  ·
    refine ⟨143226393041459601992355239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95484262027639734661570159 143226393041459601992355239)
    ·
      refine ⟨214839589562189402988532859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143226393041459601992355239 214839589562189402988532859)
      ·
        refine ⟨322259384343284104482799289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214839589562189402988532859 322259384343284104482799289)
        ·
          refine ⟨241694538257463078362099467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322259384343284104482799289 241694538257463078362099467)
          ·
            refine ⟨362541807386194617543149201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241694538257463078362099467 362541807386194617543149201)
            ·
              refine ⟨271906355539645963157361901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362541807386194617543149201 271906355539645963157361901)
              ·
                refine ⟨101964883327367236184010713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271906355539645963157361901 101964883327367236184010713)
                ·
                  refine ⟨76473662495525427138008035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101964883327367236184010713 76473662495525427138008035)
                  ·
                    refine ⟨114710493743288140707012053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76473662495525427138008035 114710493743288140707012053)
                    ·
                      refine ⟨2688527197108315797820595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114710493743288140707012053 2688527197108315797820595)
                      ·
                        rfl

theorem cell23_5235888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_5235888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235888 prefixEnd_5235888 := by exact prefixLift 5235888
  have htrace : WordTrace (prefixWord ++ tailWord_5235888) baseStart_5235888 baseEnd_5235888 := by
    simpa [prefixWord, tailWord_5235888, baseEnd_5235888] using wordTrace_append hprefix tailTrace_5235888
  have hstable : (prefixWord ++ tailWord_5235888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235888).length < 2 ^ (prefixWord ++ tailWord_5235888).sum := by decide
  have hdescent : baseEnd_5235888 < baseStart_5235888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235895 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 3, 5]
def baseStart_5235895 : Nat := 118140960795 + 5235895 * 2 ^ 59
def prefixEnd_5235895 : Nat := 4983230072969 + 3 ^ 40 * 5235895 * 2
def baseEnd_5235895 : Nat := 896176930490965756811021

theorem tailTrace_5235895 : CollatzResearch.WordTrace tailWord_5235895 prefixEnd_5235895 896176930490965756811021 := by
  unfold tailWord_5235895
  simp only [CollatzResearch.WordTrace]
  refine ⟨190968779366254109518645139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127312519577502739679096759 190968779366254109518645139)
  ·
    refine ⟨286453169049381164277967709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190968779366254109518645139 286453169049381164277967709)
    ·
      refine ⟨107419938393517936604237891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286453169049381164277967709 107419938393517936604237891)
      ·
        refine ⟨161129907590276904906356837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107419938393517936604237891 161129907590276904906356837)
        ·
          refine ⟨30211857673176919669941907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161129907590276904906356837 30211857673176919669941907)
          ·
            refine ⟨45317786509765379504912861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30211857673176919669941907 45317786509765379504912861)
            ·
              refine ⟨16994169941162017314342323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45317786509765379504912861 16994169941162017314342323)
              ·
                refine ⟨25491254911743025971513485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16994169941162017314342323 25491254911743025971513485)
                ·
                  refine ⟨9559220591903634739317557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25491254911743025971513485 9559220591903634739317557)
                  ·
                    refine ⟨896176930490965756811021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9559220591903634739317557 896176930490965756811021)
                    ·
                      rfl

theorem cell23_5235895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_5235895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235895 prefixEnd_5235895 := by exact prefixLift 5235895
  have htrace : WordTrace (prefixWord ++ tailWord_5235895) baseStart_5235895 baseEnd_5235895 := by
    simpa [prefixWord, tailWord_5235895, baseEnd_5235895] using wordTrace_append hprefix tailTrace_5235895
  have hstable : (prefixWord ++ tailWord_5235895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235895).length < 2 ^ (prefixWord ++ tailWord_5235895).sum := by decide
  have hdescent : baseEnd_5235895 < baseStart_5235895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235909 : List Nat := [1, 3, 1, 1, 1, 1, 3, 7, 1, 1, 3]
def baseStart_5235909 : Nat := 118140960795 + 5235909 * 2 ^ 59
def prefixEnd_5235909 : Nat := 4983230072969 + 3 ^ 40 * 5235909 * 2
def baseEnd_5235909 : Nat := 2688537980202060215657999

theorem tailTrace_5235909 : CollatzResearch.WordTrace tailWord_5235909 prefixEnd_5235909 2688537980202060215657999 := by
  unfold tailWord_5235909
  simp only [CollatzResearch.WordTrace]
  refine ⟨190969289988203389909654781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127312859992135593273103187 190969289988203389909654781)
  ·
    refine ⟨71613483745576271216120543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190969289988203389909654781 71613483745576271216120543)
    ·
      refine ⟨107420225618364406824180815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71613483745576271216120543 107420225618364406824180815)
      ·
        refine ⟨161130338427546610236271223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107420225618364406824180815 161130338427546610236271223)
        ·
          refine ⟨241695507641319915354406835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161130338427546610236271223 241695507641319915354406835)
          ·
            refine ⟨362543261461979873031610253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241695507641319915354406835 362543261461979873031610253)
            ·
              refine ⟨135953723048242452386853845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362543261461979873031610253 135953723048242452386853845)
              ·
                refine ⟨3186415383943182477816887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135953723048242452386853845 3186415383943182477816887)
                ·
                  refine ⟨4779623075914773716725331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186415383943182477816887 4779623075914773716725331)
                  ·
                    refine ⟨7169434613872160575087997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4779623075914773716725331 7169434613872160575087997)
                    ·
                      refine ⟨2688537980202060215657999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7169434613872160575087997 2688537980202060215657999)
                      ·
                        rfl

theorem cell23_5235909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 1, 3].length) (baseStart_5235909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235909 prefixEnd_5235909 := by exact prefixLift 5235909
  have htrace : WordTrace (prefixWord ++ tailWord_5235909) baseStart_5235909 baseEnd_5235909 := by
    simpa [prefixWord, tailWord_5235909, baseEnd_5235909] using wordTrace_append hprefix tailTrace_5235909
  have hstable : (prefixWord ++ tailWord_5235909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235909).length < 2 ^ (prefixWord ++ tailWord_5235909).sum := by decide
  have hdescent : baseEnd_5235909 < baseStart_5235909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235935 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_5235935 : Nat := 118140960795 + 5235935 * 2 ^ 59
def prefixEnd_5235935 : Nat := 4983230072969 + 3 ^ 40 * 5235935 * 2
def baseEnd_5235935 : Nat := 2688551330699077113932879

theorem tailTrace_5235935 : CollatzResearch.WordTrace tailWord_5235935 prefixEnd_5235935 2688551330699077113932879 := by
  unfold tailWord_5235935
  simp only [CollatzResearch.WordTrace]
  refine ⟨190970238286109196350101259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127313492190739464233400839 190970238286109196350101259)
  ·
    refine ⟨286455357429163794525151889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190970238286109196350101259 286455357429163794525151889)
    ·
      refine ⟨214841518071872845893863917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286455357429163794525151889 214841518071872845893863917)
      ·
        refine ⟨80565569276952317210198969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214841518071872845893863917 80565569276952317210198969)
        ·
          refine ⟨60424176957714237907649227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80565569276952317210198969 60424176957714237907649227)
          ·
            refine ⟨90636265436571356861473841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60424176957714237907649227 90636265436571356861473841)
            ·
              refine ⟨67977199077428517646105381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90636265436571356861473841 67977199077428517646105381)
              ·
                refine ⟨12745724827017847058644759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67977199077428517646105381 12745724827017847058644759)
                ·
                  refine ⟨19118587240526770587967139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12745724827017847058644759 19118587240526770587967139)
                  ·
                    refine ⟨28677880860790155881950709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19118587240526770587967139 28677880860790155881950709)
                    ·
                      refine ⟨2688551330699077113932879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28677880860790155881950709 2688551330699077113932879)
                      ·
                        rfl

theorem cell23_5235935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_5235935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235935 prefixEnd_5235935 := by exact prefixLift 5235935
  have htrace : WordTrace (prefixWord ++ tailWord_5235935) baseStart_5235935 baseEnd_5235935 := by
    simpa [prefixWord, tailWord_5235935, baseEnd_5235935] using wordTrace_append hprefix tailTrace_5235935
  have hstable : (prefixWord ++ tailWord_5235935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235935).length < 2 ^ (prefixWord ++ tailWord_5235935).sum := by decide
  have hdescent : baseEnd_5235935 < baseStart_5235935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235966 : List Nat := [4, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_5235966 : Nat := 118140960795 + 5235966 * 2 ^ 59
def prefixEnd_5235966 : Nat := 4983230072969 + 3 ^ 40 * 5235966 * 2
def baseEnd_5235966 : Nat := 2688567248599366492645237

theorem tailTrace_5235966 : CollatzResearch.WordTrace tailWord_5235966 prefixEnd_5235966 2688567248599366492645237 := by
  unfold tailWord_5235966
  simp only [CollatzResearch.WordTrace]
  refine ⟨23871421118624611080559969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127314245965997925762986501 23871421118624611080559969)
  ·
    refine ⟨17903565838968458310419977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23871421118624611080559969 17903565838968458310419977)
    ·
      refine ⟨13427674379226343732814983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17903565838968458310419977 13427674379226343732814983)
      ·
        refine ⟨20141511568839515599222475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13427674379226343732814983 20141511568839515599222475)
        ·
          refine ⟨30212267353259273398833713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20141511568839515599222475 30212267353259273398833713)
          ·
            refine ⟨22659200514944455049125285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30212267353259273398833713 22659200514944455049125285)
            ·
              refine ⟨4248600096552085321710991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22659200514944455049125285 4248600096552085321710991)
              ·
                refine ⟨6372900144828127982566487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248600096552085321710991 6372900144828127982566487)
                ·
                  refine ⟨9559350217242191973849731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6372900144828127982566487 9559350217242191973849731)
                  ·
                    refine ⟨14339025325863287960774597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9559350217242191973849731 14339025325863287960774597)
                    ·
                      refine ⟨2688567248599366492645237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14339025325863287960774597 2688567248599366492645237)
                      ·
                        rfl

theorem cell23_5235966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_5235966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235966 prefixEnd_5235966 := by exact prefixLift 5235966
  have htrace : WordTrace (prefixWord ++ tailWord_5235966) baseStart_5235966 baseEnd_5235966 := by
    simpa [prefixWord, tailWord_5235966, baseEnd_5235966] using wordTrace_append hprefix tailTrace_5235966
  have hstable : (prefixWord ++ tailWord_5235966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235966).length < 2 ^ (prefixWord ++ tailWord_5235966).sum := by decide
  have hdescent : baseEnd_5235966 < baseStart_5235966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235969 : List Nat := [1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_5235969 : Nat := 118140960795 + 5235969 * 2 ^ 59
def prefixEnd_5235969 : Nat := 4983230072969 + 3 ^ 40 * 5235969 * 2
def baseEnd_5235969 : Nat := 2688568789041329980907723

theorem tailTrace_5235969 : CollatzResearch.WordTrace tailWord_5235969 prefixEnd_5235969 2688568789041329980907723 := by
  unfold tailWord_5235969
  simp only [CollatzResearch.WordTrace]
  refine ⟨190971478367986020156838961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127314318911990680104559307 190971478367986020156838961)
  ·
    refine ⟨143228608775989515117629221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190971478367986020156838961 143228608775989515117629221)
    ·
      refine ⟨26855364145498034084555479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143228608775989515117629221 26855364145498034084555479)
      ·
        refine ⟨40283046218247051126833219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26855364145498034084555479 40283046218247051126833219)
        ·
          refine ⟨60424569327370576690249829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40283046218247051126833219 60424569327370576690249829)
          ·
            refine ⟨11329606748881983129421843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60424569327370576690249829 11329606748881983129421843)
            ·
              refine ⟨16994410123322974694132765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11329606748881983129421843 16994410123322974694132765)
              ·
                refine ⟨6372903796246115510299787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16994410123322974694132765 6372903796246115510299787)
                ·
                  refine ⟨9559355694369173265449681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6372903796246115510299787 9559355694369173265449681)
                  ·
                    refine ⟨7169516770776879949087261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9559355694369173265449681 7169516770776879949087261)
                    ·
                      refine ⟨2688568789041329980907723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7169516770776879949087261 2688568789041329980907723)
                      ·
                        rfl

theorem cell23_5235969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_5235969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235969 prefixEnd_5235969 := by exact prefixLift 5235969
  have htrace : WordTrace (prefixWord ++ tailWord_5235969) baseStart_5235969 baseEnd_5235969 := by
    simpa [prefixWord, tailWord_5235969, baseEnd_5235969] using wordTrace_append hprefix tailTrace_5235969
  have hstable : (prefixWord ++ tailWord_5235969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235969).length < 2 ^ (prefixWord ++ tailWord_5235969).sum := by decide
  have hdescent : baseEnd_5235969 < baseStart_5235969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235976 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 2, 4]
def baseStart_5235976 : Nat := 118140960795 + 5235976 * 2 ^ 59
def prefixEnd_5235976 : Nat := 4983230072969 + 3 ^ 40 * 5235976 * 2
def baseEnd_5235976 : Nat := 896190794468637151173397

theorem tailTrace_5235976 : CollatzResearch.WordTrace tailWord_5235976 prefixEnd_5235976 896190794468637151173397 := by
  unfold tailWord_5235976
  simp only [CollatzResearch.WordTrace]
  refine ⟨95485866839480330176171891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127314489119307106901562521 95485866839480330176171891)
  ·
    refine ⟨143228800259220495264257837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95485866839480330176171891 143228800259220495264257837)
    ·
      refine ⟨53710800097207685724096689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143228800259220495264257837 53710800097207685724096689)
      ·
        refine ⟨40283100072905764293072517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53710800097207685724096689 40283100072905764293072517)
        ·
          refine ⟨7553081263669830804951097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40283100072905764293072517 7553081263669830804951097)
          ·
            refine ⟨5664810947752373103713323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7553081263669830804951097 5664810947752373103713323)
            ·
              refine ⟨8497216421628559655569985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664810947752373103713323 8497216421628559655569985)
              ·
                refine ⟨6372912316221419741677489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8497216421628559655569985 6372912316221419741677489)
                ·
                  refine ⟨4779684237166064806258117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6372912316221419741677489 4779684237166064806258117)
                  ·
                    refine ⟨896190794468637151173397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4779684237166064806258117 896190794468637151173397)
                    ·
                      rfl

theorem cell23_5235976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_5235976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235976 prefixEnd_5235976 := by exact prefixLift 5235976
  have htrace : WordTrace (prefixWord ++ tailWord_5235976) baseStart_5235976 baseEnd_5235976 := by
    simpa [prefixWord, tailWord_5235976, baseEnd_5235976] using wordTrace_append hprefix tailTrace_5235976
  have hstable : (prefixWord ++ tailWord_5235976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235976).length < 2 ^ (prefixWord ++ tailWord_5235976).sum := by decide
  have hdescent : baseEnd_5235976 < baseStart_5235976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5235986 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5235986 : Nat := 118140960795 + 5235986 * 2 ^ 59
def prefixEnd_5235986 : Nat := 4983230072969 + 3 ^ 40 * 5235986 * 2
def baseEnd_5235986 : Nat := 2688577518212456414395145

theorem tailTrace_5235986 : CollatzResearch.WordTrace tailWord_5235986 prefixEnd_5235986 2688577518212456414395145 := by
  unfold tailWord_5235986
  simp only [CollatzResearch.WordTrace]
  refine ⟨47743024602231108015051953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127314732272616288040138541 47743024602231108015051953)
  ·
    refine ⟨35807268451673331011288965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47743024602231108015051953 35807268451673331011288965)
    ·
      refine ⟨6713862834688749564616681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35807268451673331011288965 6713862834688749564616681)
      ·
        refine ⟨5035397126016562173462511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6713862834688749564616681 5035397126016562173462511)
        ·
          refine ⟨7553095689024843260193767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5035397126016562173462511 7553095689024843260193767)
          ·
            refine ⟨11329643533537264890290651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553095689024843260193767 11329643533537264890290651)
            ·
              refine ⟨16994465300305897335435977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11329643533537264890290651 16994465300305897335435977)
              ·
                refine ⟨12745848975229423001576983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16994465300305897335435977 12745848975229423001576983)
                ·
                  refine ⟨19118773462844134502365475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12745848975229423001576983 19118773462844134502365475)
                  ·
                    refine ⟨28678160194266201753548213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19118773462844134502365475 28678160194266201753548213)
                    ·
                      refine ⟨2688577518212456414395145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28678160194266201753548213 2688577518212456414395145)
                      ·
                        rfl

theorem cell23_5235986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5235986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5235986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5235986 prefixEnd_5235986 := by exact prefixLift 5235986
  have htrace : WordTrace (prefixWord ++ tailWord_5235986) baseStart_5235986 baseEnd_5235986 := by
    simpa [prefixWord, tailWord_5235986, baseEnd_5235986] using wordTrace_append hprefix tailTrace_5235986
  have hstable : (prefixWord ++ tailWord_5235986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5235986).length < 2 ^ (prefixWord ++ tailWord_5235986).sum := by decide
  have hdescent : baseEnd_5235986 < baseStart_5235986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5235986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236052 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_5236052 : Nat := 118140960795 + 5236052 * 2 ^ 59
def prefixEnd_5236052 : Nat := 4983230072969 + 3 ^ 40 * 5236052 * 2
def baseEnd_5236052 : Nat := 2688611407935653156169841

theorem tailTrace_5236052 : CollatzResearch.WordTrace tailWord_5236052 prefixEnd_5236052 2688611407935653156169841 := by
  unfold tailWord_5236052
  simp only [CollatzResearch.WordTrace]
  refine ⟨95487252813342662666055205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127316337084456883554740273 95487252813342662666055205)
  ·
    refine ⟨17903859902501749249885351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95487252813342662666055205 17903859902501749249885351)
    ·
      refine ⟨26855789853752623874828027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17903859902501749249885351 26855789853752623874828027)
      ·
        refine ⟨40283684780628935812242041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26855789853752623874828027 40283684780628935812242041)
        ·
          refine ⟨30212763585471701859181531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40283684780628935812242041 30212763585471701859181531)
          ·
            refine ⟨45319145378207552788772297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30212763585471701859181531 45319145378207552788772297)
            ·
              refine ⟨33989359033655664591579223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45319145378207552788772297 33989359033655664591579223)
              ·
                refine ⟨50984038550483496887368835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33989359033655664591579223 50984038550483496887368835)
                ·
                  refine ⟨76476057825725245331053253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50984038550483496887368835 76476057825725245331053253)
                  ·
                    refine ⟨14339260842323483499572485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76476057825725245331053253 14339260842323483499572485)
                    ·
                      refine ⟨2688611407935653156169841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14339260842323483499572485 2688611407935653156169841)
                      ·
                        rfl

theorem cell23_5236052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_5236052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236052 prefixEnd_5236052 := by exact prefixLift 5236052
  have htrace : WordTrace (prefixWord ++ tailWord_5236052) baseStart_5236052 baseEnd_5236052 := by
    simpa [prefixWord, tailWord_5236052, baseEnd_5236052] using wordTrace_append hprefix tailTrace_5236052
  have hstable : (prefixWord ++ tailWord_5236052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236052).length < 2 ^ (prefixWord ++ tailWord_5236052).sum := by decide
  have hdescent : baseEnd_5236052 < baseStart_5236052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236054 : List Nat := [5, 2, 3, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5236054 : Nat := 118140960795 + 5236054 * 2 ^ 59
def prefixEnd_5236054 : Nat := 4983230072969 + 3 ^ 40 * 5236054 * 2
def baseEnd_5236054 : Nat := 2688612434896962148344833

theorem tailTrace_5236054 : CollatzResearch.WordTrace tailWord_5236054 prefixEnd_5236054 2688612434896962148344833 := by
  unfold tailWord_5236054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11935911160792379979605201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127316385715118719782455477 11935911160792379979605201)
  ·
    refine ⟨8951933370594284984703901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11935911160792379979605201 8951933370594284984703901)
    ·
      refine ⟨3356975013972856869263963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8951933370594284984703901 3356975013972856869263963)
      ·
        refine ⟨5035462520959285303895945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3356975013972856869263963 5035462520959285303895945)
        ·
          refine ⟨3776596890719463977921959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5035462520959285303895945 3776596890719463977921959)
          ·
            refine ⟨5664895336079195966882939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3776596890719463977921959 5664895336079195966882939)
            ·
              refine ⟨8497343004118793950324409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5664895336079195966882939 8497343004118793950324409)
              ·
                refine ⟨6373007253089095462743307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8497343004118793950324409 6373007253089095462743307)
                ·
                  refine ⟨9559510879633643194114961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373007253089095462743307 9559510879633643194114961)
                  ·
                    refine ⟨7169633159725232395586221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9559510879633643194114961 7169633159725232395586221)
                    ·
                      refine ⟨2688612434896962148344833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7169633159725232395586221 2688612434896962148344833)
                      ·
                        rfl

theorem cell23_5236054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5236054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236054 prefixEnd_5236054 := by exact prefixLift 5236054
  have htrace : WordTrace (prefixWord ++ tailWord_5236054) baseStart_5236054 baseEnd_5236054 := by
    simpa [prefixWord, tailWord_5236054, baseEnd_5236054] using wordTrace_append hprefix tailTrace_5236054
  have hstable : (prefixWord ++ tailWord_5236054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236054).length < 2 ^ (prefixWord ++ tailWord_5236054).sum := by decide
  have hdescent : baseEnd_5236054 < baseStart_5236054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236056 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 2, 2, 2]
def baseStart_5236056 : Nat := 118140960795 + 5236056 * 2 ^ 59
def prefixEnd_5236056 : Nat := 4983230072969 + 3 ^ 40 * 5236056 * 2
def baseEnd_5236056 : Nat := 2688613461858271140519823

theorem tailTrace_5236056 : CollatzResearch.WordTrace tailWord_5236056 prefixEnd_5236056 2688613461858271140519823 := by
  unfold tailWord_5236056
  simp only [CollatzResearch.WordTrace]
  refine ⟨95487325759335417007628011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127316434345780556010170681 95487325759335417007628011)
  ·
    refine ⟨143230988639003125511442017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95487325759335417007628011 143230988639003125511442017)
    ·
      refine ⟨107423241479252344133581513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143230988639003125511442017 107423241479252344133581513)
      ·
        refine ⟨80567431109439258100186135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107423241479252344133581513 80567431109439258100186135)
        ·
          refine ⟨120851146664158887150279203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80567431109439258100186135 120851146664158887150279203)
          ·
            refine ⟨181276719996238330725418805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120851146664158887150279203 181276719996238330725418805)
            ·
              refine ⟨16994692499647343505508013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 181276719996238330725418805 16994692499647343505508013)
              ·
                refine ⟨6373009687367753814565505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16994692499647343505508013 6373009687367753814565505)
                ·
                  refine ⟨4779757265525815360924129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6373009687367753814565505 4779757265525815360924129)
                  ·
                    refine ⟨3584817949144361520693097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4779757265525815360924129 3584817949144361520693097)
                    ·
                      refine ⟨2688613461858271140519823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584817949144361520693097 2688613461858271140519823)
                      ·
                        rfl

theorem cell23_5236056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_5236056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236056 prefixEnd_5236056 := by exact prefixLift 5236056
  have htrace : WordTrace (prefixWord ++ tailWord_5236056) baseStart_5236056 baseEnd_5236056 := by
    simpa [prefixWord, tailWord_5236056, baseEnd_5236056] using wordTrace_append hprefix tailTrace_5236056
  have hstable : (prefixWord ++ tailWord_5236056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236056).length < 2 ^ (prefixWord ++ tailWord_5236056).sum := by decide
  have hdescent : baseEnd_5236056 < baseStart_5236056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236065 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_5236065 : Nat := 118140960795 + 5236065 * 2 ^ 59
def prefixEnd_5236065 : Nat := 4983230072969 + 3 ^ 40 * 5236065 * 2
def baseEnd_5236065 : Nat := 2688618083184161605307281

theorem tailTrace_5236065 : CollatzResearch.WordTrace tailWord_5236065 prefixEnd_5236065 2688618083184161605307281 := by
  unfold tailWord_5236065
  simp only [CollatzResearch.WordTrace]
  refine ⟨190974979775638228552333649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127316653183758819034889099 190974979775638228552333649)
  ·
    refine ⟨143231234831728671414250237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190974979775638228552333649 143231234831728671414250237)
    ·
      refine ⟨53711713061898251780343839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143231234831728671414250237 53711713061898251780343839)
      ·
        refine ⟨80567569592847377670515759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53711713061898251780343839 80567569592847377670515759)
        ·
          refine ⟨120851354389271066505773639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80567569592847377670515759 120851354389271066505773639)
          ·
            refine ⟨181277031583906599758660459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120851354389271066505773639 181277031583906599758660459)
            ·
              refine ⟨271915547375859899637990689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181277031583906599758660459 271915547375859899637990689)
              ·
                refine ⟨203936660531894924728493017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271915547375859899637990689 203936660531894924728493017)
                ·
                  refine ⟨152952495398921193546369763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203936660531894924728493017 152952495398921193546369763)
                  ·
                    refine ⟨229428743098381790319554645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 152952495398921193546369763 229428743098381790319554645)
                    ·
                      refine ⟨2688618083184161605307281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 229428743098381790319554645 2688618083184161605307281)
                      ·
                        rfl

theorem cell23_5236065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_5236065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236065 prefixEnd_5236065 := by exact prefixLift 5236065
  have htrace : WordTrace (prefixWord ++ tailWord_5236065) baseStart_5236065 baseEnd_5236065 := by
    simpa [prefixWord, tailWord_5236065, baseEnd_5236065] using wordTrace_append hprefix tailTrace_5236065
  have hstable : (prefixWord ++ tailWord_5236065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236065).length < 2 ^ (prefixWord ++ tailWord_5236065).sum := by decide
  have hdescent : baseEnd_5236065 < baseStart_5236065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236092 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_5236092 : Nat := 118140960795 + 5236092 * 2 ^ 59
def prefixEnd_5236092 : Nat := 4983230072969 + 3 ^ 40 * 5236092 * 2
def baseEnd_5236092 : Nat := 896210649053944333223219

theorem tailTrace_5236092 : CollatzResearch.WordTrace tailWord_5236092 prefixEnd_5236092 896210649053944333223219 := by
  unfold tailWord_5236092
  simp only [CollatzResearch.WordTrace]
  refine ⟨95487982273270206081783265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127317309697693608109044353 95487982273270206081783265)
  ·
    refine ⟨71615986704952654561337449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95487982273270206081783265 71615986704952654561337449)
    ·
      refine ⟨53711990028714490921003087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71615986704952654561337449 53711990028714490921003087)
      ·
        refine ⟨80567985043071736381504631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53711990028714490921003087 80567985043071736381504631)
        ·
          refine ⟨120851977564607604572256947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80567985043071736381504631 120851977564607604572256947)
          ·
            refine ⟨181277966346911406858385421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120851977564607604572256947 181277966346911406858385421)
            ·
              refine ⟨67979237380091777571894533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181277966346911406858385421 67979237380091777571894533)
              ·
                refine ⟨12746107008767208294730225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67979237380091777571894533 12746107008767208294730225)
                ·
                  refine ⟨9559580256575406221047669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12746107008767208294730225 9559580256575406221047669)
                  ·
                    refine ⟨896210649053944333223219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9559580256575406221047669 896210649053944333223219)
                    ·
                      rfl

theorem cell23_5236092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_5236092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236092 prefixEnd_5236092 := by exact prefixLift 5236092
  have htrace : WordTrace (prefixWord ++ tailWord_5236092) baseStart_5236092 baseEnd_5236092 := by
    simpa [prefixWord, tailWord_5236092, baseEnd_5236092] using wordTrace_append hprefix tailTrace_5236092
  have hstable : (prefixWord ++ tailWord_5236092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236092).length < 2 ^ (prefixWord ++ tailWord_5236092).sum := by decide
  have hdescent : baseEnd_5236092 < baseStart_5236092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236095 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_5236095 : Nat := 118140960795 + 5236095 * 2 ^ 59
def prefixEnd_5236095 : Nat := 4983230072969 + 3 ^ 40 * 5236095 * 2
def baseEnd_5236095 : Nat := 2688633487603796487932143

theorem tailTrace_5236095 : CollatzResearch.WordTrace tailWord_5236095 prefixEnd_5236095 2688633487603796487932143 := by
  unfold tailWord_5236095
  simp only [CollatzResearch.WordTrace]
  refine ⟨190976073965529543675925739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127317382643686362450617159 190976073965529543675925739)
  ·
    refine ⟨286464110948294315513888609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190976073965529543675925739 286464110948294315513888609)
    ·
      refine ⟨214848083211220736635416457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286464110948294315513888609 214848083211220736635416457)
      ·
        refine ⟨161136062408415552476562343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214848083211220736635416457 161136062408415552476562343)
        ·
          refine ⟨241704093612623328714843515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161136062408415552476562343 241704093612623328714843515)
          ·
            refine ⟨362556140418934993072265273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241704093612623328714843515 362556140418934993072265273)
            ·
              refine ⟨271917105314201244804198955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362556140418934993072265273 271917105314201244804198955)
              ·
                refine ⟨407875657971301867206298433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271917105314201244804198955 407875657971301867206298433)
                ·
                  refine ⟨305906743478476400404723825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407875657971301867206298433 305906743478476400404723825)
                  ·
                    refine ⟨229430057608857300303542869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 305906743478476400404723825 229430057608857300303542869)
                    ·
                      refine ⟨2688633487603796487932143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 229430057608857300303542869 2688633487603796487932143)
                      ·
                        rfl

theorem cell23_5236095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_5236095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236095 prefixEnd_5236095 := by exact prefixLift 5236095
  have htrace : WordTrace (prefixWord ++ tailWord_5236095) baseStart_5236095 baseEnd_5236095 := by
    simpa [prefixWord, tailWord_5236095, baseEnd_5236095] using wordTrace_append hprefix tailTrace_5236095
  have hstable : (prefixWord ++ tailWord_5236095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236095).length < 2 ^ (prefixWord ++ tailWord_5236095).sum := by decide
  have hdescent : baseEnd_5236095 < baseStart_5236095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236099 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 2, 5, 2]
def baseStart_5236099 : Nat := 118140960795 + 5236099 * 2 ^ 59
def prefixEnd_5236099 : Nat := 4983230072969 + 3 ^ 40 * 5236099 * 2
def baseEnd_5236099 : Nat := 2688635541526414472282125

theorem tailTrace_5236099 : CollatzResearch.WordTrace tailWord_5236099 prefixEnd_5236099 2688635541526414472282125 := by
  unfold tailWord_5236099
  simp only [CollatzResearch.WordTrace]
  refine ⟨190976219857515052359071351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127317479905010034906047567 190976219857515052359071351)
  ·
    refine ⟨286464329786272578538607027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190976219857515052359071351 286464329786272578538607027)
    ·
      refine ⟨429696494679408867807910541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286464329786272578538607027 429696494679408867807910541)
      ·
        refine ⟨161136185504778325427966453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 429696494679408867807910541 161136185504778325427966453)
        ·
          refine ⟨15106517391072968008871855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 161136185504778325427966453 15106517391072968008871855)
          ·
            refine ⟨22659776086609452013307783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15106517391072968008871855 22659776086609452013307783)
            ·
              refine ⟨33989664129914178019961675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22659776086609452013307783 33989664129914178019961675)
              ·
                refine ⟨50984496194871267029942513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33989664129914178019961675 50984496194871267029942513)
                ·
                  refine ⟨38238372146153450272456885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50984496194871267029942513 38238372146153450272456885)
                  ·
                    refine ⟨3584847388701885963042833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38238372146153450272456885 3584847388701885963042833)
                    ·
                      refine ⟨2688635541526414472282125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3584847388701885963042833 2688635541526414472282125)
                      ·
                        rfl

theorem cell23_5236099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_5236099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236099 prefixEnd_5236099 := by exact prefixLift 5236099
  have htrace : WordTrace (prefixWord ++ tailWord_5236099) baseStart_5236099 baseEnd_5236099 := by
    simpa [prefixWord, tailWord_5236099, baseEnd_5236099] using wordTrace_append hprefix tailTrace_5236099
  have hstable : (prefixWord ++ tailWord_5236099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236099).length < 2 ^ (prefixWord ++ tailWord_5236099).sum := by decide
  have hdescent : baseEnd_5236099 < baseStart_5236099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236126 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5236126 : Nat := 118140960795 + 5236126 * 2 ^ 59
def prefixEnd_5236126 : Nat := 4983230072969 + 3 ^ 40 * 5236126 * 2
def baseEnd_5236126 : Nat := 896216468501361955548167

theorem tailTrace_5236126 : CollatzResearch.WordTrace tailWord_5236126 prefixEnd_5236126 896216468501361955548167 := by
  unfold tailWord_5236126
  simp only [CollatzResearch.WordTrace]
  refine ⟨23872150578552154496288029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127318136418944823980202821 23872150578552154496288029)
  ·
    refine ⟨8952056466957057936108011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23872150578552154496288029 8952056466957057936108011)
    ·
      refine ⟨13428084700435586904162017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8952056466957057936108011 13428084700435586904162017)
      ·
        refine ⟨10071063525326690178121513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13428084700435586904162017 10071063525326690178121513)
        ·
          refine ⟨7553297643995017633591135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10071063525326690178121513 7553297643995017633591135)
          ·
            refine ⟨11329946465992526450386703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553297643995017633591135 11329946465992526450386703)
            ·
              refine ⟨16994919698988789675580055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11329946465992526450386703 16994919698988789675580055)
              ·
                refine ⟨25492379548483184513370083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16994919698988789675580055 25492379548483184513370083)
                ·
                  refine ⟨38238569322724776770055125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25492379548483184513370083 38238569322724776770055125)
                  ·
                    refine ⟨896216468501361955548167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38238569322724776770055125 896216468501361955548167)
                    ·
                      rfl

theorem cell23_5236126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5236126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236126 prefixEnd_5236126 := by exact prefixLift 5236126
  have htrace : WordTrace (prefixWord ++ tailWord_5236126) baseStart_5236126 baseEnd_5236126 := by
    simpa [prefixWord, tailWord_5236126, baseEnd_5236126] using wordTrace_append hprefix tailTrace_5236126
  have hstable : (prefixWord ++ tailWord_5236126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236126).length < 2 ^ (prefixWord ++ tailWord_5236126).sum := by decide
  have hdescent : baseEnd_5236126 < baseStart_5236126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236236 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_5236236 : Nat := 118140960795 + 5236236 * 2 ^ 59
def prefixEnd_5236236 : Nat := 4983230072969 + 3 ^ 40 * 5236236 * 2
def baseEnd_5236236 : Nat := 2688705888376080436268995

theorem tailTrace_5236236 : CollatzResearch.WordTrace tailWord_5236236 prefixEnd_5236236 2688705888376080436268995 := by
  unfold tailWord_5236236
  simp only [CollatzResearch.WordTrace]
  refine ⟨95490608329009362378404281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127320811105345816504539041 95490608329009362378404281)
  ·
    refine ⟨71617956246757021783803211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95490608329009362378404281 71617956246757021783803211)
    ·
      refine ⟨107426934370135532675704817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71617956246757021783803211 107426934370135532675704817)
      ·
        refine ⟨80570200777601649506778613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107426934370135532675704817 80570200777601649506778613)
        ·
          refine ⟨7553456322900154641260495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80570200777601649506778613 7553456322900154641260495)
          ·
            refine ⟨11330184484350231961890743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7553456322900154641260495 11330184484350231961890743)
            ·
              refine ⟨16995276726525347942836115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11330184484350231961890743 16995276726525347942836115)
              ·
                refine ⟨25492915089788021914254173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16995276726525347942836115 25492915089788021914254173)
                ·
                  refine ⟨9559843158670508217845315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25492915089788021914254173 9559843158670508217845315)
                  ·
                    refine ⟨14339764738005762326767973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9559843158670508217845315 14339764738005762326767973)
                    ·
                      refine ⟨2688705888376080436268995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14339764738005762326767973 2688705888376080436268995)
                      ·
                        rfl

theorem cell23_5236236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_5236236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236236 prefixEnd_5236236 := by exact prefixLift 5236236
  have htrace : WordTrace (prefixWord ++ tailWord_5236236) baseStart_5236236 baseEnd_5236236 := by
    simpa [prefixWord, tailWord_5236236, baseEnd_5236236] using wordTrace_append hprefix tailTrace_5236236
  have hstable : (prefixWord ++ tailWord_5236236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236236).length < 2 ^ (prefixWord ++ tailWord_5236236).sum := by decide
  have hdescent : baseEnd_5236236 < baseStart_5236236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236253 : List Nat := [1, 4, 2, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_5236253 : Nat := 118140960795 + 5236253 * 2 ^ 59
def prefixEnd_5236253 : Nat := 4983230072969 + 3 ^ 40 * 5236253 * 2
def baseEnd_5236253 : Nat := 2688714617547206869756417

theorem tailTrace_5236253 : CollatzResearch.WordTrace tailWord_5236253 prefixEnd_5236253 2688714617547206869756417 := by
  unfold tailWord_5236253
  simp only [CollatzResearch.WordTrace]
  refine ⟨190981836698957136660177413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127321224465971424440118275 190981836698957136660177413)
  ·
    refine ⟨35809094381054463123783265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190981836698957136660177413 35809094381054463123783265)
    ·
      refine ⟨26856820785790847342837449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35809094381054463123783265 26856820785790847342837449)
      ·
        refine ⟨20142615589343135507128087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26856820785790847342837449 20142615589343135507128087)
        ·
          refine ⟨30213923384014703260692131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20142615589343135507128087 30213923384014703260692131)
          ·
            refine ⟨45320885076022054891038197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30213923384014703260692131 45320885076022054891038197)
            ·
              refine ⟨4248832975877067646034831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45320885076022054891038197 4248832975877067646034831)
              ·
                refine ⟨6373249463815601469052247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248832975877067646034831 6373249463815601469052247)
                ·
                  refine ⟨9559874195723402203578371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373249463815601469052247 9559874195723402203578371)
                  ·
                    refine ⟨14339811293585103305367557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9559874195723402203578371 14339811293585103305367557)
                    ·
                      refine ⟨2688714617547206869756417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14339811293585103305367557 2688714617547206869756417)
                      ·
                        rfl

theorem cell23_5236253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_5236253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236253 prefixEnd_5236253 := by exact prefixLift 5236253
  have htrace : WordTrace (prefixWord ++ tailWord_5236253) baseStart_5236253 baseEnd_5236253 := by
    simpa [prefixWord, tailWord_5236253, baseEnd_5236253] using wordTrace_append hprefix tailTrace_5236253
  have hstable : (prefixWord ++ tailWord_5236253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236253).length < 2 ^ (prefixWord ++ tailWord_5236253).sum := by decide
  have hdescent : baseEnd_5236253 < baseStart_5236253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236256 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5236256 : Nat := 118140960795 + 5236256 * 2 ^ 59
def prefixEnd_5236256 : Nat := 4983230072969 + 3 ^ 40 * 5236256 * 2
def baseEnd_5236256 : Nat := 2688716157989170358018903

theorem tailTrace_5236256 : CollatzResearch.WordTrace tailWord_5236256 prefixEnd_5236256 2688716157989170358018903 := by
  unfold tailWord_5236256
  simp only [CollatzResearch.WordTrace]
  refine ⟨95490973058973134086268311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127321297411964178781691081 95490973058973134086268311)
  ·
    refine ⟨143236459588459701129402467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95490973058973134086268311 143236459588459701129402467)
    ·
      refine ⟨214854689382689551694103701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143236459588459701129402467 214854689382689551694103701)
      ·
        refine ⟨10071313564813572735661111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 214854689382689551694103701 10071313564813572735661111)
        ·
          refine ⟨15106970347220359103491667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10071313564813572735661111 15106970347220359103491667)
          ·
            refine ⟨22660455520830538655237501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15106970347220359103491667 22660455520830538655237501)
            ·
              refine ⟨8497670820311451995714063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22660455520830538655237501 8497670820311451995714063)
              ·
                refine ⟨12746506230467177993571095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8497670820311451995714063 12746506230467177993571095)
                ·
                  refine ⟨19119759345700766990356643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12746506230467177993571095 19119759345700766990356643)
                  ·
                    refine ⟨28679639018551150485534965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19119759345700766990356643 28679639018551150485534965)
                    ·
                      refine ⟨2688716157989170358018903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28679639018551150485534965 2688716157989170358018903)
                      ·
                        rfl

theorem cell23_5236256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5236256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236256 prefixEnd_5236256 := by exact prefixLift 5236256
  have htrace : WordTrace (prefixWord ++ tailWord_5236256) baseStart_5236256 baseEnd_5236256 := by
    simpa [prefixWord, tailWord_5236256, baseEnd_5236256] using wordTrace_append hprefix tailTrace_5236256
  have hstable : (prefixWord ++ tailWord_5236256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236256).length < 2 ^ (prefixWord ++ tailWord_5236256).sum := by decide
  have hdescent : baseEnd_5236256 < baseStart_5236256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236259 : List Nat := [1, 1, 1, 4, 6, 10]
def baseStart_5236259 : Nat := 118140960795 + 5236259 * 2 ^ 59
def prefixEnd_5236259 : Nat := 4983230072969 + 3 ^ 40 * 5236259 * 2
def baseEnd_5236259 : Nat := 11064681886547875910623

theorem tailTrace_5236259 : CollatzResearch.WordTrace tailWord_5236259 prefixEnd_5236259 11064681886547875910623 := by
  unfold tailWord_5236259
  simp only [CollatzResearch.WordTrace]
  refine ⟨190982055536935399684895831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127321370357956933123263887 190982055536935399684895831)
  ·
    refine ⟨286473083305403099527343747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190982055536935399684895831 286473083305403099527343747)
    ·
      refine ⟨429709624958104649291015621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286473083305403099527343747 429709624958104649291015621)
      ·
        refine ⟨80570554679644621742065429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 429709624958104649291015621 80570554679644621742065429)
        ·
          refine ⟨3776744750608341644159317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80570554679644621742065429 3776744750608341644159317)
          ·
            refine ⟨11064681886547875910623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3776744750608341644159317 11064681886547875910623)
            ·
              rfl

theorem cell23_5236259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 10].length) (baseStart_5236259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236259 prefixEnd_5236259 := by exact prefixLift 5236259
  have htrace : WordTrace (prefixWord ++ tailWord_5236259) baseStart_5236259 baseEnd_5236259 := by
    simpa [prefixWord, tailWord_5236259, baseEnd_5236259] using wordTrace_append hprefix tailTrace_5236259
  have hstable : (prefixWord ++ tailWord_5236259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236259).length < 2 ^ (prefixWord ++ tailWord_5236259).sum := by decide
  have hdescent : baseEnd_5236259 < baseStart_5236259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236264 : List Nat := [2, 1, 5, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_5236264 : Nat := 118140960795 + 5236264 * 2 ^ 59
def prefixEnd_5236264 : Nat := 4983230072969 + 3 ^ 40 * 5236264 * 2
def baseEnd_5236264 : Nat := 2688720265834406326718867

theorem tailTrace_5236264 : CollatzResearch.WordTrace tailWord_5236264 prefixEnd_5236264 2688720265834406326718867 := by
  unfold tailWord_5236264
  simp only [CollatzResearch.WordTrace]
  refine ⟨95491118950958642769413923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127321491934611523692551897 95491118950958642769413923)
  ·
    refine ⟨143236678426437964154120885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95491118950958642769413923 143236678426437964154120885)
    ·
      refine ⟨13428438602478559139448833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143236678426437964154120885 13428438602478559139448833)
      ·
        refine ⟨10071328951858919354586625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13428438602478559139448833 10071328951858919354586625)
        ·
          refine ⟨7553496713894189515939969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10071328951858919354586625 7553496713894189515939969)
          ·
            refine ⟨5665122535420642136954977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7553496713894189515939969 5665122535420642136954977)
            ·
              refine ⟨4248841901565481602716233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5665122535420642136954977 4248841901565481602716233)
              ·
                refine ⟨3186631426174111202037175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4248841901565481602716233 3186631426174111202037175)
                ·
                  refine ⟨4779947139261166803055763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186631426174111202037175 4779947139261166803055763)
                  ·
                    refine ⟨7169920708891750204583645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4779947139261166803055763 7169920708891750204583645)
                    ·
                      refine ⟨2688720265834406326718867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7169920708891750204583645 2688720265834406326718867)
                      ·
                        rfl

theorem cell23_5236264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_5236264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236264 prefixEnd_5236264 := by exact prefixLift 5236264
  have htrace : WordTrace (prefixWord ++ tailWord_5236264) baseStart_5236264 baseEnd_5236264 := by
    simpa [prefixWord, tailWord_5236264, baseEnd_5236264] using wordTrace_append hprefix tailTrace_5236264
  have hstable : (prefixWord ++ tailWord_5236264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236264).length < 2 ^ (prefixWord ++ tailWord_5236264).sum := by decide
  have hdescent : baseEnd_5236264 < baseStart_5236264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236289 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 2, 7]
def baseStart_5236289 : Nat := 118140960795 + 5236289 * 2 ^ 59
def prefixEnd_5236289 : Nat := 4983230072969 + 3 ^ 40 * 5236289 * 2
def baseEnd_5236289 : Nat := 896244367616922909635417

theorem tailTrace_5236289 : CollatzResearch.WordTrace tailWord_5236289 prefixEnd_5236289 896244367616922909635417 := by
  unfold tailWord_5236289
  simp only [CollatzResearch.WordTrace]
  refine ⟨190983149726826714808487921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127322099817884476538991947 190983149726826714808487921)
  ·
    refine ⟨143237362295120036106365941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190983149726826714808487921 143237362295120036106365941)
    ·
      refine ⟨13428502715167503384971807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143237362295120036106365941 13428502715167503384971807)
      ·
        refine ⟨20142754072751255077457711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13428502715167503384971807 20142754072751255077457711)
        ·
          refine ⟨30214131109126882616186567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20142754072751255077457711 30214131109126882616186567)
          ·
            refine ⟨45321196663690323924279851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30214131109126882616186567 45321196663690323924279851)
            ·
              refine ⟨67981794995535485886419777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45321196663690323924279851 67981794995535485886419777)
              ·
                refine ⟨50986346246651614414814833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67981794995535485886419777 50986346246651614414814833)
                ·
                  refine ⟨38239759684988710811111125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50986346246651614414814833 38239759684988710811111125)
                  ·
                    refine ⟨896244367616922909635417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38239759684988710811111125 896244367616922909635417)
                    ·
                      rfl

theorem cell23_5236289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_5236289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236289 prefixEnd_5236289 := by exact prefixLift 5236289
  have htrace : WordTrace (prefixWord ++ tailWord_5236289) baseStart_5236289 baseEnd_5236289 := by
    simpa [prefixWord, tailWord_5236289, baseEnd_5236289] using wordTrace_append hprefix tailTrace_5236289
  have hstable : (prefixWord ++ tailWord_5236289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236289).length < 2 ^ (prefixWord ++ tailWord_5236289).sum := by decide
  have hdescent : baseEnd_5236289 < baseStart_5236289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236329 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 3]
def baseStart_5236329 : Nat := 118140960795 + 5236329 * 2 ^ 59
def prefixEnd_5236329 : Nat := 4983230072969 + 3 ^ 40 * 5236329 * 2
def baseEnd_5236329 : Nat := 2688753642076948572406067

theorem tailTrace_5236329 : CollatzResearch.WordTrace tailWord_5236329 prefixEnd_5236329 2688753642076948572406067 := by
  unfold tailWord_5236329
  simp only [CollatzResearch.WordTrace]
  refine ⟨190984608646681801639944041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127323072431121201093296027 190984608646681801639944041)
  ·
    refine ⟨143238456485011351229958031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190984608646681801639944041 143238456485011351229958031)
    ·
      refine ⟨214857684727517026844937047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143238456485011351229958031 214857684727517026844937047)
      ·
        refine ⟨322286527091275540267405571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214857684727517026844937047 322286527091275540267405571)
        ·
          refine ⟨483429790636913310401108357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322286527091275540267405571 483429790636913310401108357)
          ·
            refine ⟨90643085744421245700207817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 483429790636913310401108357 90643085744421245700207817)
            ·
              refine ⟨67982314308315934275155863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90643085744421245700207817 67982314308315934275155863)
              ·
                refine ⟨101973471462473901412733795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67982314308315934275155863 101973471462473901412733795)
                ·
                  refine ⟨152960207193710852119100693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101973471462473901412733795 152960207193710852119100693)
                  ·
                    refine ⟨7170009712205196193082845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 152960207193710852119100693 7170009712205196193082845)
                    ·
                      refine ⟨2688753642076948572406067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7170009712205196193082845 2688753642076948572406067)
                      ·
                        rfl

theorem cell23_5236329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_5236329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236329 prefixEnd_5236329 := by exact prefixLift 5236329
  have htrace : WordTrace (prefixWord ++ tailWord_5236329) baseStart_5236329 baseEnd_5236329 := by
    simpa [prefixWord, tailWord_5236329, baseEnd_5236329] using wordTrace_append hprefix tailTrace_5236329
  have hstable : (prefixWord ++ tailWord_5236329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236329).length < 2 ^ (prefixWord ++ tailWord_5236329).sum := by decide
  have hdescent : baseEnd_5236329 < baseStart_5236329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236389 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_5236389 : Nat := 118140960795 + 5236389 * 2 ^ 59
def prefixEnd_5236389 : Nat := 4983230072969 + 3 ^ 40 * 5236389 * 2
def baseEnd_5236389 : Nat := 2688784450916218337655791

theorem tailTrace_5236389 : CollatzResearch.WordTrace tailWord_5236389 prefixEnd_5236389 2688784450916218337655791 := by
  unfold tailWord_5236389
  simp only [CollatzResearch.WordTrace]
  refine ⟨190986797026464431887128221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127324531350976287924752147 190986797026464431887128221)
  ·
    refine ⟨71620048884924161957673083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190986797026464431887128221 71620048884924161957673083)
    ·
      refine ⟨107430073327386242936509625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71620048884924161957673083 107430073327386242936509625)
      ·
        refine ⟨80572554995539682202382219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107430073327386242936509625 80572554995539682202382219)
        ·
          refine ⟨120858832493309523303573329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80572554995539682202382219 120858832493309523303573329)
          ·
            refine ⟨90644124369982142477679997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120858832493309523303573329 90644124369982142477679997)
            ·
              refine ⟨33991546638743303429129999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90644124369982142477679997 33991546638743303429129999)
              ·
                refine ⟨50987319958114955143694999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33991546638743303429129999 50987319958114955143694999)
                ·
                  refine ⟨76480979937172432715542499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50987319958114955143694999 76480979937172432715542499)
                  ·
                    refine ⟨114721469905758649073313749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76480979937172432715542499 114721469905758649073313749)
                    ·
                      refine ⟨2688784450916218337655791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114721469905758649073313749 2688784450916218337655791)
                      ·
                        rfl

theorem cell23_5236389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_5236389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236389 prefixEnd_5236389 := by exact prefixLift 5236389
  have htrace : WordTrace (prefixWord ++ tailWord_5236389) baseStart_5236389 baseEnd_5236389 := by
    simpa [prefixWord, tailWord_5236389, baseEnd_5236389] using wordTrace_append hprefix tailTrace_5236389
  have hstable : (prefixWord ++ tailWord_5236389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236389).length < 2 ^ (prefixWord ++ tailWord_5236389).sum := by decide
  have hdescent : baseEnd_5236389 < baseStart_5236389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236409 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 2, 8]
def baseStart_5236409 : Nat := 118140960795 + 5236409 * 2 ^ 59
def prefixEnd_5236409 : Nat := 4983230072969 + 3 ^ 40 * 5236409 * 2
def baseEnd_5236409 : Nat := 896264906843102753135233

theorem tailTrace_5236409 : CollatzResearch.WordTrace tailWord_5236409 prefixEnd_5236409 896264906843102753135233 := by
  unfold tailWord_5236409
  simp only [CollatzResearch.WordTrace]
  refine ⟨190987526486391975302856281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127325017657594650201904187 190987526486391975302856281)
  ·
    refine ⟨143240644864793981477142211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190987526486391975302856281 143240644864793981477142211)
    ·
      refine ⟨214860967297190972215713317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143240644864793981477142211 214860967297190972215713317)
      ·
        refine ⟨40286431368223307290446247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214860967297190972215713317 40286431368223307290446247)
        ·
          refine ⟨60429647052334960935669371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40286431368223307290446247 60429647052334960935669371)
          ·
            refine ⟨90644470578502441403504057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60429647052334960935669371 90644470578502441403504057)
            ·
              refine ⟨67983352933876831052628043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90644470578502441403504057 67983352933876831052628043)
              ·
                refine ⟨101975029400815246578942065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67983352933876831052628043 101975029400815246578942065)
                ·
                  refine ⟨76481272050611434934206549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101975029400815246578942065 76481272050611434934206549)
                  ·
                    refine ⟨896264906843102753135233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76481272050611434934206549 896264906843102753135233)
                    ·
                      rfl

theorem cell23_5236409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_5236409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236409 prefixEnd_5236409 := by exact prefixLift 5236409
  have htrace : WordTrace (prefixWord ++ tailWord_5236409) baseStart_5236409 baseEnd_5236409 := by
    simpa [prefixWord, tailWord_5236409, baseEnd_5236409] using wordTrace_append hprefix tailTrace_5236409
  have hstable : (prefixWord ++ tailWord_5236409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236409).length < 2 ^ (prefixWord ++ tailWord_5236409).sum := by decide
  have hdescent : baseEnd_5236409 < baseStart_5236409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236470 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_5236470 : Nat := 118140960795 + 5236470 * 2 ^ 59
def prefixEnd_5236470 : Nat := 4983230072969 + 3 ^ 40 * 5236470 * 2
def baseEnd_5236470 : Nat := 2688826042849232520742919

theorem tailTrace_5236470 : CollatzResearch.WordTrace tailWord_5236470 prefixEnd_5236470 2688826042849232520742919 := by
  unfold tailWord_5236470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11936859458698186420051679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127326500892780655147217909 11936859458698186420051679)
  ·
    refine ⟨17905289188047279630077519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11936859458698186420051679 17905289188047279630077519)
    ·
      refine ⟨26857933782070919445116279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17905289188047279630077519 26857933782070919445116279)
      ·
        refine ⟨40286900673106379167674419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26857933782070919445116279 40286900673106379167674419)
        ·
          refine ⟨60430351009659568751511629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40286900673106379167674419 60430351009659568751511629)
          ·
            refine ⟨22661381628622338281816861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60430351009659568751511629 22661381628622338281816861)
            ·
              refine ⟨8498018110733376855681323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22661381628622338281816861 8498018110733376855681323)
              ·
                refine ⟨12747027166100065283521985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8498018110733376855681323 12747027166100065283521985)
                ·
                  refine ⟨9560270374575048962641489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12747027166100065283521985 9560270374575048962641489)
                  ·
                    refine ⟨7170202780931286721981117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9560270374575048962641489 7170202780931286721981117)
                    ·
                      refine ⟨2688826042849232520742919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7170202780931286721981117 2688826042849232520742919)
                      ·
                        rfl

theorem cell23_5236470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_5236470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236470 prefixEnd_5236470 := by exact prefixLift 5236470
  have htrace : WordTrace (prefixWord ++ tailWord_5236470) baseStart_5236470 baseEnd_5236470 := by
    simpa [prefixWord, tailWord_5236470, baseEnd_5236470] using wordTrace_append hprefix tailTrace_5236470
  have hstable : (prefixWord ++ tailWord_5236470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236470).length < 2 ^ (prefixWord ++ tailWord_5236470).sum := by decide
  have hdescent : baseEnd_5236470 < baseStart_5236470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236520 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5236520 : Nat := 118140960795 + 5236520 * 2 ^ 59
def prefixEnd_5236520 : Nat := 4983230072969 + 3 ^ 40 * 5236520 * 2
def baseEnd_5236520 : Nat := 896283905627319108372563

theorem tailTrace_5236520 : CollatzResearch.WordTrace tailWord_5236520 prefixEnd_5236520 896283905627319108372563 := by
  unfold tailWord_5236520
  simp only [CollatzResearch.WordTrace]
  refine ⟨95495787494494920630073507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127327716659326560840098009 95495787494494920630073507)
  ·
    refine ⟨143243681241742380945110261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95495787494494920630073507 143243681241742380945110261)
    ·
      refine ⟨13429095116413348213604087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 143243681241742380945110261 13429095116413348213604087)
      ·
        refine ⟨20143642674620022320406131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13429095116413348213604087 20143642674620022320406131)
        ·
          refine ⟨30215464011930033480609197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20143642674620022320406131 30215464011930033480609197)
          ·
            refine ⟨11330799004473762555228449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30215464011930033480609197 11330799004473762555228449)
            ·
              refine ⟨8498099253355321916421337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11330799004473762555228449 8498099253355321916421337)
              ·
                refine ⟨6373574440016491437316003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8498099253355321916421337 6373574440016491437316003)
                ·
                  refine ⟨9560361660024737155974005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373574440016491437316003 9560361660024737155974005)
                  ·
                    refine ⟨896283905627319108372563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9560361660024737155974005 896283905627319108372563)
                    ·
                      rfl

theorem cell23_5236520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5236520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236520 prefixEnd_5236520 := by exact prefixLift 5236520
  have htrace : WordTrace (prefixWord ++ tailWord_5236520) baseStart_5236520 baseEnd_5236520 := by
    simpa [prefixWord, tailWord_5236520, baseEnd_5236520] using wordTrace_append hprefix tailTrace_5236520
  have hstable : (prefixWord ++ tailWord_5236520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236520).length < 2 ^ (prefixWord ++ tailWord_5236520).sum := by decide
  have hdescent : baseEnd_5236520 < baseStart_5236520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236540 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_5236540 : Nat := 118140960795 + 5236540 * 2 ^ 59
def prefixEnd_5236540 : Nat := 4983230072969 + 3 ^ 40 * 5236540 * 2
def baseEnd_5236540 : Nat := 2688861986495047246867597

theorem tailTrace_5236540 : CollatzResearch.WordTrace tailWord_5236540 prefixEnd_5236540 2688861986495047246867597 := by
  unfold tailWord_5236540
  simp only [CollatzResearch.WordTrace]
  refine ⟨95496152224458692337937537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127328202965944923117250049 95496152224458692337937537)
  ·
    refine ⟨71622114168344019253453153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95496152224458692337937537 71622114168344019253453153)
    ·
      refine ⟨53716585626258014440089865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71622114168344019253453153 53716585626258014440089865)
      ·
        refine ⟨40287439219693510830067399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53716585626258014440089865 40287439219693510830067399)
        ·
          refine ⟨60431158829540266245101099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40287439219693510830067399 60431158829540266245101099)
          ·
            refine ⟨90646738244310399367651649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60431158829540266245101099 90646738244310399367651649)
            ·
              refine ⟨67985053683232799525738737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90646738244310399367651649 67985053683232799525738737)
              ·
                refine ⟨50988790262424599644304053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67985053683232799525738737 50988790262424599644304053)
                ·
                  refine ⟨4780199087102306216653505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50988790262424599644304053 4780199087102306216653505)
                  ·
                    refine ⟨3585149315326729662490129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4780199087102306216653505 3585149315326729662490129)
                    ·
                      refine ⟨2688861986495047246867597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585149315326729662490129 2688861986495047246867597)
                      ·
                        rfl

theorem cell23_5236540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_5236540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236540 prefixEnd_5236540 := by exact prefixLift 5236540
  have htrace : WordTrace (prefixWord ++ tailWord_5236540) baseStart_5236540 baseEnd_5236540 := by
    simpa [prefixWord, tailWord_5236540, baseEnd_5236540] using wordTrace_append hprefix tailTrace_5236540
  have hstable : (prefixWord ++ tailWord_5236540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236540).length < 2 ^ (prefixWord ++ tailWord_5236540).sum := by decide
  have hdescent : baseEnd_5236540 < baseStart_5236540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236590 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_5236590 : Nat := 118140960795 + 5236590 * 2 ^ 59
def prefixEnd_5236590 : Nat := 4983230072969 + 3 ^ 40 * 5236590 * 2
def baseEnd_5236590 : Nat := 2688887660527772051242367

theorem tailTrace_5236590 : CollatzResearch.WordTrace tailWord_5236590 prefixEnd_5236590 2688887660527772051242367 := by
  unfold tailWord_5236590
  simp only [CollatzResearch.WordTrace]
  refine ⟨23874266012342030401899403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127329418732490828810130149 23874266012342030401899403)
  ·
    refine ⟨35811399018513045602849105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23874266012342030401899403 35811399018513045602849105)
    ·
      refine ⟨26858549263884784202136829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35811399018513045602849105 26858549263884784202136829)
      ·
        refine ⟨10071955973956794075801311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26858549263884784202136829 10071955973956794075801311)
        ·
          refine ⟨15107933960935191113701967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10071955973956794075801311 15107933960935191113701967)
          ·
            refine ⟨22661900941402786670552951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15107933960935191113701967 22661900941402786670552951)
            ·
              refine ⟨33992851412104180005829427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22661900941402786670552951 33992851412104180005829427)
              ·
                refine ⟨50989277118156270008744141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33992851412104180005829427 50989277118156270008744141)
                ·
                  refine ⟨19120978919308601253279053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50989277118156270008744141 19120978919308601253279053)
                  ·
                    refine ⟨7170367094740725469979645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19120978919308601253279053 7170367094740725469979645)
                    ·
                      refine ⟨2688887660527772051242367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7170367094740725469979645 2688887660527772051242367)
                      ·
                        rfl

theorem cell23_5236590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_5236590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236590 prefixEnd_5236590 := by exact prefixLift 5236590
  have htrace : WordTrace (prefixWord ++ tailWord_5236590) baseStart_5236590 baseEnd_5236590 := by
    simpa [prefixWord, tailWord_5236590, baseEnd_5236590] using wordTrace_append hprefix tailTrace_5236590
  have hstable : (prefixWord ++ tailWord_5236590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236590).length < 2 ^ (prefixWord ++ tailWord_5236590).sum := by decide
  have hdescent : baseEnd_5236590 < baseStart_5236590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236647 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_5236647 : Nat := 118140960795 + 5236647 * 2 ^ 59
def prefixEnd_5236647 : Nat := 4983230072969 + 3 ^ 40 * 5236647 * 2
def baseEnd_5236647 : Nat := 2688916928925078328229605

theorem tailTrace_5236647 : CollatzResearch.WordTrace tailWord_5236647 prefixEnd_5236647 2688916928925078328229605 := by
  unfold tailWord_5236647
  simp only [CollatzResearch.WordTrace]
  refine ⟨190996207059529741950020195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127330804706353161300013463 190996207059529741950020195)
  ·
    refine ⟨286494310589294612925030293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190996207059529741950020195 286494310589294612925030293)
    ·
      refine ⟨13429420808873184980860795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 286494310589294612925030293 13429420808873184980860795)
      ·
        refine ⟨20144131213309777471291193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13429420808873184980860795 20144131213309777471291193)
        ·
          refine ⟨15108098409982333103468395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20144131213309777471291193 15108098409982333103468395)
          ·
            refine ⟨22662147614973499655202593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15108098409982333103468395 22662147614973499655202593)
            ·
              refine ⟨16996610711230124741401945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22662147614973499655202593 16996610711230124741401945)
              ·
                refine ⟨12747458033422593556051459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16996610711230124741401945 12747458033422593556051459)
                ·
                  refine ⟨19121187050133890334077189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12747458033422593556051459 19121187050133890334077189)
                  ·
                    refine ⟨3585222571900104437639473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19121187050133890334077189 3585222571900104437639473)
                    ·
                      refine ⟨2688916928925078328229605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585222571900104437639473 2688916928925078328229605)
                      ·
                        rfl

theorem cell23_5236647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_5236647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236647 prefixEnd_5236647 := by exact prefixLift 5236647
  have htrace : WordTrace (prefixWord ++ tailWord_5236647) baseStart_5236647 baseEnd_5236647 := by
    simpa [prefixWord, tailWord_5236647, baseEnd_5236647] using wordTrace_append hprefix tailTrace_5236647
  have hstable : (prefixWord ++ tailWord_5236647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236647).length < 2 ^ (prefixWord ++ tailWord_5236647).sum := by decide
  have hdescent : baseEnd_5236647 < baseStart_5236647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236670 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_5236670 : Nat := 118140960795 + 5236670 * 2 ^ 59
def prefixEnd_5236670 : Nat := 4983230072969 + 3 ^ 40 * 5236670 * 2
def baseEnd_5236670 : Nat := 298769859886681304249111

theorem tailTrace_5236670 : CollatzResearch.WordTrace tailWord_5236670 prefixEnd_5236670 298769859886681304249111 := by
  unfold tailWord_5236670
  simp only [CollatzResearch.WordTrace]
  refine ⟨23874630742305802109763433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127331363958964277918738309 23874630742305802109763433)
  ·
    refine ⟨17905973056729351582322575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23874630742305802109763433 17905973056729351582322575)
    ·
      refine ⟨26858959585094027373483863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17905973056729351582322575 26858959585094027373483863)
      ·
        refine ⟨40288439377641041060225795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26858959585094027373483863 40288439377641041060225795)
        ·
          refine ⟨60432659066461561590338693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40288439377641041060225795 60432659066461561590338693)
          ·
            refine ⟨11331123574961542798188505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60432659066461561590338693 11331123574961542798188505)
            ·
              refine ⟨8498342681221157098641379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11331123574961542798188505 8498342681221157098641379)
              ·
                refine ⟨12747514021831735647962069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8498342681221157098641379 12747514021831735647962069)
                ·
                  refine ⟨298769859886681304249111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12747514021831735647962069 298769859886681304249111)
                  ·
                    rfl

theorem cell23_5236670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_5236670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236670 prefixEnd_5236670 := by exact prefixLift 5236670
  have htrace : WordTrace (prefixWord ++ tailWord_5236670) baseStart_5236670 baseEnd_5236670 := by
    simpa [prefixWord, tailWord_5236670, baseEnd_5236670] using wordTrace_append hprefix tailTrace_5236670
  have hstable : (prefixWord ++ tailWord_5236670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236670).length < 2 ^ (prefixWord ++ tailWord_5236670).sum := by decide
  have hdescent : baseEnd_5236670 < baseStart_5236670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236680 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_5236680 : Nat := 118140960795 + 5236680 * 2 ^ 59
def prefixEnd_5236680 : Nat := 4983230072969 + 3 ^ 40 * 5236680 * 2
def baseEnd_5236680 : Nat := 2688933873786676699116953

theorem tailTrace_5236680 : CollatzResearch.WordTrace tailWord_5236680 prefixEnd_5236680 2688933873786676699116953 := by
  unfold tailWord_5236680
  simp only [CollatzResearch.WordTrace]
  refine ⟨95498705334205094292985747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127331607112273459057314329 95498705334205094292985747)
  ·
    refine ⟨143248058001307641439478621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95498705334205094292985747 143248058001307641439478621)
    ·
      refine ⟨53718021750490365539804483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143248058001307641439478621 53718021750490365539804483)
      ·
        refine ⟨80577032625735548309706725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53718021750490365539804483 80577032625735548309706725)
        ·
          refine ⟨15108193617325415308070011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80577032625735548309706725 15108193617325415308070011)
          ·
            refine ⟨22662290425988122962105017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15108193617325415308070011 22662290425988122962105017)
            ·
              refine ⟨16996717819491092221578763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22662290425988122962105017 16996717819491092221578763)
              ·
                refine ⟨25495076729236638332368145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16996717819491092221578763 25495076729236638332368145)
                ·
                  refine ⟨19121307546927478749276109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25495076729236638332368145 19121307546927478749276109)
                  ·
                    refine ⟨7170490330097804530978541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19121307546927478749276109 7170490330097804530978541)
                    ·
                      refine ⟨2688933873786676699116953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7170490330097804530978541 2688933873786676699116953)
                      ·
                        rfl

theorem cell23_5236680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_5236680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236680 prefixEnd_5236680 := by exact prefixLift 5236680
  have htrace : WordTrace (prefixWord ++ tailWord_5236680) baseStart_5236680 baseEnd_5236680 := by
    simpa [prefixWord, tailWord_5236680, baseEnd_5236680] using wordTrace_append hprefix tailTrace_5236680
  have hstable : (prefixWord ++ tailWord_5236680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236680).length < 2 ^ (prefixWord ++ tailWord_5236680).sum := by decide
  have hdescent : baseEnd_5236680 < baseStart_5236680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236720 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 4, 4, 2]
def baseStart_5236720 : Nat := 118140960795 + 5236720 * 2 ^ 59
def prefixEnd_5236720 : Nat := 4983230072969 + 3 ^ 40 * 5236720 * 2
def baseEnd_5236720 : Nat := 2688954413012856542616769

theorem tailTrace_5236720 : CollatzResearch.WordTrace tailWord_5236720 prefixEnd_5236720 2688954413012856542616769 := by
  unfold tailWord_5236720
  simp only [CollatzResearch.WordTrace]
  refine ⟨95499434794132637708713807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127332579725510183611618409 95499434794132637708713807)
  ·
    refine ⟨143249152191198956563070711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95499434794132637708713807 143249152191198956563070711)
    ·
      refine ⟨214873728286798434844606067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143249152191198956563070711 214873728286798434844606067)
      ·
        refine ⟨322310592430197652266909101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214873728286798434844606067 322310592430197652266909101)
        ·
          refine ⟨120866472161324119600090913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 322310592430197652266909101 120866472161324119600090913)
          ·
            refine ⟨90649854120993089700068185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120866472161324119600090913 90649854120993089700068185)
            ·
              refine ⟨67987390590744817275051139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90649854120993089700068185 67987390590744817275051139)
              ·
                refine ⟨101981085886117225912576709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67987390590744817275051139 101981085886117225912576709)
                ·
                  refine ⟨19121453603646979858608133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101981085886117225912576709 19121453603646979858608133)
                  ·
                    refine ⟨3585272550683808723489025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19121453603646979858608133 3585272550683808723489025)
                    ·
                      refine ⟨2688954413012856542616769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585272550683808723489025 2688954413012856542616769)
                      ·
                        rfl

theorem cell23_5236720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 4, 2].length) (baseStart_5236720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236720 prefixEnd_5236720 := by exact prefixLift 5236720
  have htrace : WordTrace (prefixWord ++ tailWord_5236720) baseStart_5236720 baseEnd_5236720 := by
    simpa [prefixWord, tailWord_5236720, baseEnd_5236720] using wordTrace_append hprefix tailTrace_5236720
  have hstable : (prefixWord ++ tailWord_5236720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236720).length < 2 ^ (prefixWord ++ tailWord_5236720).sum := by decide
  have hdescent : baseEnd_5236720 < baseStart_5236720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236733 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_5236733 : Nat := 118140960795 + 5236733 * 2 ^ 59
def prefixEnd_5236733 : Nat := 4983230072969 + 3 ^ 40 * 5236733 * 2
def baseEnd_5236733 : Nat := 2688961088261364991754209

theorem tailTrace_5236733 : CollatzResearch.WordTrace tailWord_5236733 prefixEnd_5236733 2688961088261364991754209 := by
  unfold tailWord_5236733
  simp only [CollatzResearch.WordTrace]
  refine ⟨190999343737218178637650853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127332895824812119091767235 190999343737218178637650853)
  ·
    refine ⟨35812376950728408494559535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190999343737218178637650853 35812376950728408494559535)
    ·
      refine ⟨53718565426092612741839303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35812376950728408494559535 53718565426092612741839303)
      ·
        refine ⟨80577848139138919112758955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53718565426092612741839303 80577848139138919112758955)
        ·
          refine ⟨120866772208708378669138433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80577848139138919112758955 120866772208708378669138433)
          ·
            refine ⟨90650079156531284001853825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120866772208708378669138433 90650079156531284001853825)
            ·
              refine ⟨67987559367398463001390369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90650079156531284001853825 67987559367398463001390369)
              ·
                refine ⟨50990669525548847251042777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67987559367398463001390369 50990669525548847251042777)
                ·
                  refine ⟨38243002144161635438282083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50990669525548847251042777 38243002144161635438282083)
                  ·
                    refine ⟨57364503216242453157423125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38243002144161635438282083 57364503216242453157423125)
                    ·
                      refine ⟨2688961088261364991754209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57364503216242453157423125 2688961088261364991754209)
                      ·
                        rfl

theorem cell23_5236733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_5236733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236733 prefixEnd_5236733 := by exact prefixLift 5236733
  have htrace : WordTrace (prefixWord ++ tailWord_5236733) baseStart_5236733 baseEnd_5236733 := by
    simpa [prefixWord, tailWord_5236733, baseEnd_5236733] using wordTrace_append hprefix tailTrace_5236733
  have hstable : (prefixWord ++ tailWord_5236733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236733).length < 2 ^ (prefixWord ++ tailWord_5236733).sum := by decide
  have hdescent : baseEnd_5236733 < baseStart_5236733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236797 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_5236797 : Nat := 118140960795 + 5236797 * 2 ^ 59
def prefixEnd_5236797 : Nat := 4983230072969 + 3 ^ 40 * 5236797 * 2
def baseEnd_5236797 : Nat := 2688993951023252741353915

theorem tailTrace_5236797 : CollatzResearch.WordTrace tailWord_5236797 prefixEnd_5236797 2688993951023252741353915 := by
  unfold tailWord_5236797
  simp only [CollatzResearch.WordTrace]
  refine ⟨191001678008986317567980645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127334452005990878378653763 191001678008986317567980645)
  ·
    refine ⟨35812814626684934543996371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191001678008986317567980645 35812814626684934543996371)
    ·
      refine ⟨53719221940027401815994557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35812814626684934543996371 53719221940027401815994557)
      ·
        refine ⟨20144708227510275680997959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53719221940027401815994557 20144708227510275680997959)
        ·
          refine ⟨30217062341265413521496939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20144708227510275680997959 30217062341265413521496939)
          ·
            refine ⟨45325593511898120282245409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30217062341265413521496939 45325593511898120282245409)
            ·
              refine ⟨33994195133923590211684057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45325593511898120282245409 33994195133923590211684057)
              ·
                refine ⟨25495646350442692658763043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33994195133923590211684057 25495646350442692658763043)
                ·
                  refine ⟨38243469525664038988144565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25495646350442692658763043 38243469525664038988144565)
                  ·
                    refine ⟨3585325268031003655138553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38243469525664038988144565 3585325268031003655138553)
                    ·
                      refine ⟨2688993951023252741353915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585325268031003655138553 2688993951023252741353915)
                      ·
                        rfl

theorem cell23_5236797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_5236797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236797 prefixEnd_5236797 := by exact prefixLift 5236797
  have htrace : WordTrace (prefixWord ++ tailWord_5236797) baseStart_5236797 baseEnd_5236797 := by
    simpa [prefixWord, tailWord_5236797, baseEnd_5236797] using wordTrace_append hprefix tailTrace_5236797
  have hstable : (prefixWord ++ tailWord_5236797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236797).length < 2 ^ (prefixWord ++ tailWord_5236797).sum := by decide
  have hdescent : baseEnd_5236797 < baseStart_5236797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236814 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_5236814 : Nat := 118140960795 + 5236814 * 2 ^ 59
def prefixEnd_5236814 : Nat := 4983230072969 + 3 ^ 40 * 5236814 * 2
def baseEnd_5236814 : Nat := 2689002680194379174841337

theorem tailTrace_5236814 : CollatzResearch.WordTrace tailWord_5236814 prefixEnd_5236814 2689002680194379174841337 := by
  unfold tailWord_5236814
  simp only [CollatzResearch.WordTrace]
  refine ⟨23875287256240591183918687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127334865366616486314232997 23875287256240591183918687)
  ·
    refine ⟨35812930884360886775878031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23875287256240591183918687 35812930884360886775878031)
    ·
      refine ⟨53719396326541330163817047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35812930884360886775878031 53719396326541330163817047)
      ·
        refine ⟨80579094489811995245725571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53719396326541330163817047 80579094489811995245725571)
        ·
          refine ⟨120868641734717992868588357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80579094489811995245725571 120868641734717992868588357)
          ·
            refine ⟨22662870325259623662860317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120868641734717992868588357 22662870325259623662860317)
            ·
              refine ⟨8498576371972358873572619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22662870325259623662860317 8498576371972358873572619)
              ·
                refine ⟨12747864557958538310358929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8498576371972358873572619 12747864557958538310358929)
                ·
                  refine ⟨9560898418468903732769197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12747864557958538310358929 9560898418468903732769197)
                  ·
                    refine ⟨3585336906925838899788449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9560898418468903732769197 3585336906925838899788449)
                    ·
                      refine ⟨2689002680194379174841337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585336906925838899788449 2689002680194379174841337)
                      ·
                        rfl

theorem cell23_5236814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_5236814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236814 prefixEnd_5236814 := by exact prefixLift 5236814
  have htrace : WordTrace (prefixWord ++ tailWord_5236814) baseStart_5236814 baseEnd_5236814 := by
    simpa [prefixWord, tailWord_5236814, baseEnd_5236814] using wordTrace_append hprefix tailTrace_5236814
  have hstable : (prefixWord ++ tailWord_5236814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236814).length < 2 ^ (prefixWord ++ tailWord_5236814).sum := by decide
  have hdescent : baseEnd_5236814 < baseStart_5236814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236821 : List Nat := [1, 3, 2, 2, 1, 4, 2, 3, 1, 1, 3]
def baseStart_5236821 : Nat := 118140960795 + 5236821 * 2 ^ 59
def prefixEnd_5236821 : Nat := 4983230072969 + 3 ^ 40 * 5236821 * 2
def baseEnd_5236821 : Nat := 2689006274558960647453805

theorem tailTrace_5236821 : CollatzResearch.WordTrace tailWord_5236821 prefixEnd_5236821 2689006274558960647453805 := by
  unfold tailWord_5236821
  simp only [CollatzResearch.WordTrace]
  refine ⟨191002553360899369666854317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127335035573932913111236211 191002553360899369666854317)
  ·
    refine ⟨71625957510337263625070369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191002553360899369666854317 71625957510337263625070369)
    ·
      refine ⟨53719468132752947718802777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71625957510337263625070369 53719468132752947718802777)
      ·
        refine ⟨40289601099564710789102083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53719468132752947718802777 40289601099564710789102083)
        ·
          refine ⟨60434401649347066183653125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40289601099564710789102083 60434401649347066183653125)
          ·
            refine ⟨11331450309252574909434961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60434401649347066183653125 11331450309252574909434961)
            ·
              refine ⟨8498587731939431182076221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11331450309252574909434961 8498587731939431182076221)
              ·
                refine ⟨3186970399477286693278583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8498587731939431182076221 3186970399477286693278583)
                ·
                  refine ⟨4780455599215930039917875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3186970399477286693278583 4780455599215930039917875)
                  ·
                    refine ⟨7170683398823895059876813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4780455599215930039917875 7170683398823895059876813)
                    ·
                      refine ⟨2689006274558960647453805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7170683398823895059876813 2689006274558960647453805)
                      ·
                        rfl

theorem cell23_5236821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_5236821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236821 prefixEnd_5236821 := by exact prefixLift 5236821
  have htrace : WordTrace (prefixWord ++ tailWord_5236821) baseStart_5236821 baseEnd_5236821 := by
    simpa [prefixWord, tailWord_5236821, baseEnd_5236821] using wordTrace_append hprefix tailTrace_5236821
  have hstable : (prefixWord ++ tailWord_5236821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236821).length < 2 ^ (prefixWord ++ tailWord_5236821).sum := by decide
  have hdescent : baseEnd_5236821 < baseStart_5236821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236824 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 1, 5]
def baseStart_5236824 : Nat := 118140960795 + 5236824 * 2 ^ 59
def prefixEnd_5236824 : Nat := 4983230072969 + 3 ^ 40 * 5236824 * 2
def baseEnd_5236824 : Nat := 896335938333641378572097

theorem tailTrace_5236824 : CollatzResearch.WordTrace tailWord_5236824 prefixEnd_5236824 896335938333641378572097 := by
  unfold tailWord_5236824
  simp only [CollatzResearch.WordTrace]
  refine ⟨95501331389944250589606763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127335108519925667452809017 95501331389944250589606763)
  ·
    refine ⟨143251997084916375884410145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95501331389944250589606763 143251997084916375884410145)
    ·
      refine ⟨107438997813687281913307609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143251997084916375884410145 107438997813687281913307609)
      ·
        refine ⟨80579248360265461434980707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107438997813687281913307609 80579248360265461434980707)
        ·
          refine ⟨120868872540398192152471061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80579248360265461434980707 120868872540398192152471061)
          ·
            refine ⟨5665728400331165257147081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120868872540398192152471061 5665728400331165257147081)
            ·
              refine ⟨4249296300248373942860311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5665728400331165257147081 4249296300248373942860311)
              ·
                refine ⟨6373944450372560914290467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4249296300248373942860311 6373944450372560914290467)
                ·
                  refine ⟨9560916675558841371435701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6373944450372560914290467 9560916675558841371435701)
                  ·
                    refine ⟨896335938333641378572097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9560916675558841371435701 896335938333641378572097)
                    ·
                      rfl

theorem cell23_5236824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_5236824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236824 prefixEnd_5236824 := by exact prefixLift 5236824
  have htrace : WordTrace (prefixWord ++ tailWord_5236824) baseStart_5236824 baseEnd_5236824 := by
    simpa [prefixWord, tailWord_5236824, baseEnd_5236824] using wordTrace_append hprefix tailTrace_5236824
  have hstable : (prefixWord ++ tailWord_5236824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236824).length < 2 ^ (prefixWord ++ tailWord_5236824).sum := by decide
  have hdescent : baseEnd_5236824 < baseStart_5236824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236837 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_5236837 : Nat := 118140960795 + 5236837 * 2 ^ 59
def prefixEnd_5236837 : Nat := 4983230072969 + 3 ^ 40 * 5236837 * 2
def baseEnd_5236837 : Nat := 896338163416477528284577

theorem tailTrace_5236837 : CollatzResearch.WordTrace tailWord_5236837 prefixEnd_5236837 896338163416477528284577 := by
  unfold tailWord_5236837
  simp only [CollatzResearch.WordTrace]
  refine ⟨191003136928841404399436765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127335424619227602932957843 191003136928841404399436765)
  ·
    refine ⟨71626176348315526649788787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191003136928841404399436765 71626176348315526649788787)
    ·
      refine ⟨107439264522473289974683181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71626176348315526649788787 107439264522473289974683181)
      ·
        refine ⟨40289724195927483740506193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107439264522473289974683181 40289724195927483740506193)
        ·
          refine ⟨30217293146945612805379645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40289724195927483740506193 30217293146945612805379645)
          ·
            refine ⟨11331484930104604802017367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30217293146945612805379645 11331484930104604802017367)
            ·
              refine ⟨16997227395156907203026051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11331484930104604802017367 16997227395156907203026051)
              ·
                refine ⟨25495841092735360804539077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16997227395156907203026051 25495841092735360804539077)
                ·
                  refine ⟨4780470204887880150851077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25495841092735360804539077 4780470204887880150851077)
                  ·
                    refine ⟨896338163416477528284577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4780470204887880150851077 896338163416477528284577)
                    ·
                      rfl

theorem cell23_5236837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_5236837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236837 prefixEnd_5236837 := by exact prefixLift 5236837
  have htrace : WordTrace (prefixWord ++ tailWord_5236837) baseStart_5236837 baseEnd_5236837 := by
    simpa [prefixWord, tailWord_5236837, baseEnd_5236837] using wordTrace_append hprefix tailTrace_5236837
  have hstable : (prefixWord ++ tailWord_5236837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236837).length < 2 ^ (prefixWord ++ tailWord_5236837).sum := by decide
  have hdescent : baseEnd_5236837 < baseStart_5236837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236844 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 3, 2, 2]
def baseStart_5236844 : Nat := 118140960795 + 5236844 * 2 ^ 59
def prefixEnd_5236844 : Nat := 4983230072969 + 3 ^ 40 * 5236844 * 2
def baseEnd_5236844 : Nat := 2689018084614014057466199

theorem tailTrace_5236844 : CollatzResearch.WordTrace tailWord_5236844 prefixEnd_5236844 2689018084614014057466199 := by
  unfold tailWord_5236844
  simp only [CollatzResearch.WordTrace]
  refine ⟨95501696119908022297470793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127335594826544029729961057 95501696119908022297470793)
  ·
    refine ⟨71626272089931016723103095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95501696119908022297470793 71626272089931016723103095)
    ·
      refine ⟨107439408134896525084654643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71626272089931016723103095 107439408134896525084654643)
      ·
        refine ⟨161159112202344787626981965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107439408134896525084654643 161159112202344787626981965)
        ·
          refine ⟨60434667075879295360118237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161159112202344787626981965 60434667075879295360118237)
          ·
            refine ⟨22663000153454735760044339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60434667075879295360118237 22663000153454735760044339)
            ·
              refine ⟨33994500230182103640066509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22663000153454735760044339 33994500230182103640066509)
              ·
                refine ⟨12747937586318288865024941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33994500230182103640066509 12747937586318288865024941)
                ·
                  refine ⟨4780476594869358324384353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12747937586318288865024941 4780476594869358324384353)
                  ·
                    refine ⟨3585357446152018743288265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4780476594869358324384353 3585357446152018743288265)
                    ·
                      refine ⟨2689018084614014057466199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585357446152018743288265 2689018084614014057466199)
                      ·
                        rfl

theorem cell23_5236844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_5236844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236844 prefixEnd_5236844 := by exact prefixLift 5236844
  have htrace : WordTrace (prefixWord ++ tailWord_5236844) baseStart_5236844 baseEnd_5236844 := by
    simpa [prefixWord, tailWord_5236844, baseEnd_5236844] using wordTrace_append hprefix tailTrace_5236844
  have hstable : (prefixWord ++ tailWord_5236844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236844).length < 2 ^ (prefixWord ++ tailWord_5236844).sum := by decide
  have hdescent : baseEnd_5236844 < baseStart_5236844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236854 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_5236854 : Nat := 118140960795 + 5236854 * 2 ^ 59
def prefixEnd_5236854 : Nat := 4983230072969 + 3 ^ 40 * 5236854 * 2
def baseEnd_5236854 : Nat := 896341073140186339447051

theorem tailTrace_5236854 : CollatzResearch.WordTrace tailWord_5236854 prefixEnd_5236854 896341073140186339447051 := by
  unfold tailWord_5236854
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937734810611238518925351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127335837979853210868537077 11937734810611238518925351)
  ·
    refine ⟨17906602215916857778388027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11937734810611238518925351 17906602215916857778388027)
    ·
      refine ⟨26859903323875286667582041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17906602215916857778388027 26859903323875286667582041)
      ·
        refine ⟨20144927492906465000686531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26859903323875286667582041 20144927492906465000686531)
        ·
          refine ⟨30217391239359697501029797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20144927492906465000686531 30217391239359697501029797)
          ·
            refine ⟨5665760857379943281443087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30217391239359697501029797 5665760857379943281443087)
            ·
              refine ⟨8498641286069914922164631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5665760857379943281443087 8498641286069914922164631)
              ·
                refine ⟨12747961929104872383246947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8498641286069914922164631 12747961929104872383246947)
                ·
                  refine ⟨19121942893657308574870421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12747961929104872383246947 19121942893657308574870421)
                  ·
                    refine ⟨896341073140186339447051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19121942893657308574870421 896341073140186339447051)
                    ·
                      rfl

theorem cell23_5236854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_5236854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236854 prefixEnd_5236854 := by exact prefixLift 5236854
  have htrace : WordTrace (prefixWord ++ tailWord_5236854) baseStart_5236854 baseEnd_5236854 := by
    simpa [prefixWord, tailWord_5236854, baseEnd_5236854] using wordTrace_append hprefix tailTrace_5236854
  have hstable : (prefixWord ++ tailWord_5236854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236854).length < 2 ^ (prefixWord ++ tailWord_5236854).sum := by decide
  have hdescent : baseEnd_5236854 < baseStart_5236854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236857 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 4]
def baseStart_5236857 : Nat := 118140960795 + 5236857 * 2 ^ 59
def prefixEnd_5236857 : Nat := 4983230072969 + 3 ^ 40 * 5236857 * 2
def baseEnd_5236857 : Nat := 2689024759862522506603639

theorem tailTrace_5236857 : CollatzResearch.WordTrace tailWord_5236857 prefixEnd_5236857 2689024759862522506603639 := by
  unfold tailWord_5236857
  simp only [CollatzResearch.WordTrace]
  refine ⟨191003866388768947815164825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127335910925845965210109883 191003866388768947815164825)
  ·
    refine ⟨143252899791576710861373619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191003866388768947815164825 143252899791576710861373619)
    ·
      refine ⟨214879349687365066292060429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143252899791576710861373619 214879349687365066292060429)
      ·
        refine ⟨80579756132761899859522661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214879349687365066292060429 80579756132761899859522661)
        ·
          refine ⟨15108704274892856223660499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80579756132761899859522661 15108704274892856223660499)
          ·
            refine ⟨22663056412339284335490749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15108704274892856223660499 22663056412339284335490749)
            ·
              refine ⟨8498646154627231625809031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22663056412339284335490749 8498646154627231625809031)
              ·
                refine ⟨12747969231940847438713547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8498646154627231625809031 12747969231940847438713547)
                ·
                  refine ⟨19121953847911271158070321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12747969231940847438713547 19121953847911271158070321)
                  ·
                    refine ⟨14341465385933453368552741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19121953847911271158070321 14341465385933453368552741)
                    ·
                      refine ⟨2689024759862522506603639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14341465385933453368552741 2689024759862522506603639)
                      ·
                        rfl

theorem cell23_5236857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_5236857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236857 prefixEnd_5236857 := by exact prefixLift 5236857
  have htrace : WordTrace (prefixWord ++ tailWord_5236857) baseStart_5236857 baseEnd_5236857 := by
    simpa [prefixWord, tailWord_5236857, baseEnd_5236857] using wordTrace_append hprefix tailTrace_5236857
  have hstable : (prefixWord ++ tailWord_5236857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236857).length < 2 ^ (prefixWord ++ tailWord_5236857).sum := by decide
  have hdescent : baseEnd_5236857 < baseStart_5236857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236867 : List Nat := [1, 1, 1, 3, 3, 5, 2, 7]
def baseStart_5236867 : Nat := 118140960795 + 5236867 * 2 ^ 59
def prefixEnd_5236867 : Nat := 4983230072969 + 3 ^ 40 * 5236867 * 2
def baseEnd_5236867 : Nat := 99593699802558054351059

theorem tailTrace_5236867 : CollatzResearch.WordTrace tailWord_5236867 prefixEnd_5236867 99593699802558054351059 := by
  unfold tailWord_5236867
  simp only [CollatzResearch.WordTrace]
  refine ⟨191004231118732719523028855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127336154079155146348685903 191004231118732719523028855)
  ·
    refine ⟨286506346678099079284543283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191004231118732719523028855 286506346678099079284543283)
    ·
      refine ⟨429759520017148618926814925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286506346678099079284543283 429759520017148618926814925)
      ·
        refine ⟨161159820006430732097555597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 429759520017148618926814925 161159820006430732097555597)
        ·
          refine ⟨60434932502411524536583349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161159820006430732097555597 60434932502411524536583349)
          ·
            refine ⟨5665774922101080425304689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60434932502411524536583349 5665774922101080425304689)
            ·
              refine ⟨4249331191575810318978517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5665774922101080425304689 4249331191575810318978517)
              ·
                refine ⟨99593699802558054351059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4249331191575810318978517 99593699802558054351059)
                ·
                  rfl

theorem cell23_5236867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 7].length) (baseStart_5236867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236867 prefixEnd_5236867 := by exact prefixLift 5236867
  have htrace : WordTrace (prefixWord ++ tailWord_5236867) baseStart_5236867 baseEnd_5236867 := by
    simpa [prefixWord, tailWord_5236867, baseEnd_5236867] using wordTrace_append hprefix tailTrace_5236867
  have hstable : (prefixWord ++ tailWord_5236867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236867).length < 2 ^ (prefixWord ++ tailWord_5236867).sum := by decide
  have hdescent : baseEnd_5236867 < baseStart_5236867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236884 : List Nat := [2, 4, 2, 3, 1, 2, 9]
def baseStart_5236884 : Nat := 118140960795 + 5236884 * 2 ^ 59
def prefixEnd_5236884 : Nat := 4983230072969 + 3 ^ 40 * 5236884 * 2
def baseEnd_5236884 : Nat := 33198007701730788900815

theorem tailTrace_5236884 : CollatzResearch.WordTrace tailWord_5236884 prefixEnd_5236884 33198007701730788900815 := by
  unfold tailWord_5236884
  simp only [CollatzResearch.WordTrace]
  refine ⟨95502425579835565713198853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127336567439780754284265137 95502425579835565713198853)
  ·
    refine ⟨17906704796219168571224785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95502425579835565713198853 17906704796219168571224785)
    ·
      refine ⟨13430028597164376428418589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17906704796219168571224785 13430028597164376428418589)
      ·
        refine ⟨5036260723936641160656971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13430028597164376428418589 5036260723936641160656971)
        ·
          refine ⟨7554391085904961740985457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036260723936641160656971 7554391085904961740985457)
          ·
            refine ⟨5665793314428721305739093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7554391085904961740985457 5665793314428721305739093)
            ·
              refine ⟨33198007701730788900815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5665793314428721305739093 33198007701730788900815)
              ·
                rfl

theorem cell23_5236884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 9].length) (baseStart_5236884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236884 prefixEnd_5236884 := by exact prefixLift 5236884
  have htrace : WordTrace (prefixWord ++ tailWord_5236884) baseStart_5236884 baseEnd_5236884 := by
    simpa [prefixWord, tailWord_5236884, baseEnd_5236884] using wordTrace_append hprefix tailTrace_5236884
  have hstable : (prefixWord ++ tailWord_5236884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236884).length < 2 ^ (prefixWord ++ tailWord_5236884).sum := by decide
  have hdescent : baseEnd_5236884 < baseStart_5236884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236895 : List Nat := [1, 1, 2, 6, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5236895 : Nat := 118140960795 + 5236895 * 2 ^ 59
def prefixEnd_5236895 : Nat := 4983230072969 + 3 ^ 40 * 5236895 * 2
def baseEnd_5236895 : Nat := 2689044272127393357928465

theorem tailTrace_5236895 : CollatzResearch.WordTrace tailWord_5236895 prefixEnd_5236895 2689044272127393357928465 := by
  unfold tailWord_5236895
  simp only [CollatzResearch.WordTrace]
  refine ⟨191005252362631280305048139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127336834908420853536698759 191005252362631280305048139)
  ·
    refine ⟨286507878543946920457572209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191005252362631280305048139 286507878543946920457572209)
    ·
      refine ⟨214880908907960190343179157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286507878543946920457572209 214880908907960190343179157)
      ·
        refine ⟨10072542605060633922336523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 214880908907960190343179157 10072542605060633922336523)
        ·
          refine ⟨15108813907590950883504785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10072542605060633922336523 15108813907590950883504785)
          ·
            refine ⟨11331610430693213162628589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15108813907590950883504785 11331610430693213162628589)
            ·
              refine ⟨4249353911509954935985721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11331610430693213162628589 4249353911509954935985721)
              ·
                refine ⟨3187015433632466201989291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4249353911509954935985721 3187015433632466201989291)
                ·
                  refine ⟨4780523150448699302983937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187015433632466201989291 4780523150448699302983937)
                  ·
                    refine ⟨3585392362836524477237953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4780523150448699302983937 3585392362836524477237953)
                    ·
                      refine ⟨2689044272127393357928465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585392362836524477237953 2689044272127393357928465)
                      ·
                        rfl

theorem cell23_5236895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5236895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236895 prefixEnd_5236895 := by exact prefixLift 5236895
  have htrace : WordTrace (prefixWord ++ tailWord_5236895) baseStart_5236895 baseEnd_5236895 := by
    simpa [prefixWord, tailWord_5236895, baseEnd_5236895] using wordTrace_append hprefix tailTrace_5236895
  have hstable : (prefixWord ++ tailWord_5236895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236895).length < 2 ^ (prefixWord ++ tailWord_5236895).sum := by decide
  have hdescent : baseEnd_5236895 < baseStart_5236895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5236920 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_5236920 : Nat := 118140960795 + 5236920 * 2 ^ 59
def prefixEnd_5236920 : Nat := 4983230072969 + 3 ^ 40 * 5236920 * 2
def baseEnd_5236920 : Nat := 2689057109143755760115849

theorem tailTrace_5236920 : CollatzResearch.WordTrace tailWord_5236920 prefixEnd_5236920 2689057109143755760115849 := by
  unfold tailWord_5236920
  simp only [CollatzResearch.WordTrace]
  refine ⟨95503082093770354787354107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127337442791693806383138809 95503082093770354787354107)
  ·
    refine ⟨143254623140655532181031161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95503082093770354787354107 143254623140655532181031161)
    ·
      refine ⟨107440967355491649135773371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143254623140655532181031161 107440967355491649135773371)
      ·
        refine ⟨161161451033237473703660057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107440967355491649135773371 161161451033237473703660057)
        ·
          refine ⟨120871088274928105277745043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161161451033237473703660057 120871088274928105277745043)
          ·
            refine ⟨181306632412392157916617565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120871088274928105277745043 181306632412392157916617565)
            ·
              refine ⟨67989987154647059218731587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181306632412392157916617565 67989987154647059218731587)
              ·
                refine ⟨101984980731970588828097381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67989987154647059218731587 101984980731970588828097381)
                ·
                  refine ⟨19122183887244485405268259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101984980731970588828097381 19122183887244485405268259)
                  ·
                    refine ⟨28683275830866728107902389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19122183887244485405268259 28683275830866728107902389)
                    ·
                      refine ⟨2689057109143755760115849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28683275830866728107902389 2689057109143755760115849)
                      ·
                        rfl

theorem cell23_5236920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_5236920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5236920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5236920 prefixEnd_5236920 := by exact prefixLift 5236920
  have htrace : WordTrace (prefixWord ++ tailWord_5236920) baseStart_5236920 baseEnd_5236920 := by
    simpa [prefixWord, tailWord_5236920, baseEnd_5236920] using wordTrace_append hprefix tailTrace_5236920
  have hstable : (prefixWord ++ tailWord_5236920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5236920).length < 2 ^ (prefixWord ++ tailWord_5236920).sum := by decide
  have hdescent : baseEnd_5236920 < baseStart_5236920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5236920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237007 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_5237007 : Nat := 118140960795 + 5237007 * 2 ^ 59
def prefixEnd_5237007 : Nat := 4983230072969 + 3 ^ 40 * 5237007 * 2
def baseEnd_5237007 : Nat := 2689101781960696919727949

theorem tailTrace_5237007 : CollatzResearch.WordTrace tailWord_5237007 prefixEnd_5237007 2689101781960696919727949 := by
  unfold tailWord_5237007
  simp only [CollatzResearch.WordTrace]
  refine ⟨191009337338225523433125275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127339558225483682288750183 191009337338225523433125275)
  ·
    refine ⟨286514006007338285149687913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191009337338225523433125275 286514006007338285149687913)
    ·
      refine ⟨214885504505503713862265935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286514006007338285149687913 214885504505503713862265935)
      ·
        refine ⟨322328256758255570793398903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214885504505503713862265935 322328256758255570793398903)
        ·
          refine ⟨483492385137383356190098355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322328256758255570793398903 483492385137383356190098355)
          ·
            refine ⟨725238577706075034285147533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483492385137383356190098355 725238577706075034285147533)
            ·
              refine ⟨271964466639778137856930325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725238577706075034285147533 271964466639778137856930325)
              ·
                refine ⟨12748334373739600212043609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 271964466639778137856930325 12748334373739600212043609)
                ·
                  refine ⟨9561250780304700159032707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12748334373739600212043609 9561250780304700159032707)
                  ·
                    refine ⟨14341876170457050238549061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9561250780304700159032707 14341876170457050238549061)
                    ·
                      refine ⟨2689101781960696919727949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14341876170457050238549061 2689101781960696919727949)
                      ·
                        rfl

theorem cell23_5237007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_5237007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237007 prefixEnd_5237007 := by exact prefixLift 5237007
  have htrace : WordTrace (prefixWord ++ tailWord_5237007) baseStart_5237007 baseEnd_5237007 := by
    simpa [prefixWord, tailWord_5237007, baseEnd_5237007] using wordTrace_append hprefix tailTrace_5237007
  have hstable : (prefixWord ++ tailWord_5237007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237007).length < 2 ^ (prefixWord ++ tailWord_5237007).sum := by decide
  have hdescent : baseEnd_5237007 < baseStart_5237007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237027 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 3]
def baseStart_5237027 : Nat := 118140960795 + 5237027 * 2 ^ 59
def prefixEnd_5237027 : Nat := 4983230072969 + 3 ^ 40 * 5237027 * 2
def baseEnd_5237027 : Nat := 2689112051573786841477857

theorem tailTrace_5237027 : CollatzResearch.WordTrace tailWord_5237027 prefixEnd_5237027 2689112051573786841477857 := by
  unfold tailWord_5237027
  simp only [CollatzResearch.WordTrace]
  refine ⟨191010066798153066848853335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127340044532102044565902223 191010066798153066848853335)
  ·
    refine ⟨286515100197229600273280003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191010066798153066848853335 286515100197229600273280003)
    ·
      refine ⟨429772650295844400409920005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286515100197229600273280003 429772650295844400409920005)
      ·
        refine ⟨80582371930470825076860001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 429772650295844400409920005 80582371930470825076860001)
        ·
          refine ⟨60436778947853118807645001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80582371930470825076860001 60436778947853118807645001)
          ·
            refine ⟨45327584210889839105733751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60436778947853118807645001 45327584210889839105733751)
            ·
              refine ⟨67991376316334758658600627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45327584210889839105733751 67991376316334758658600627)
              ·
                refine ⟨101987064474502137987900941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67991376316334758658600627 101987064474502137987900941)
                ·
                  refine ⟨38245149177938301745462853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101987064474502137987900941 38245149177938301745462853)
                  ·
                    refine ⟨7170965470863431577274285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38245149177938301745462853 7170965470863431577274285)
                    ·
                      refine ⟨2689112051573786841477857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7170965470863431577274285 2689112051573786841477857)
                      ·
                        rfl

theorem cell23_5237027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_5237027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237027 prefixEnd_5237027 := by exact prefixLift 5237027
  have htrace : WordTrace (prefixWord ++ tailWord_5237027) baseStart_5237027 baseEnd_5237027 := by
    simpa [prefixWord, tailWord_5237027, baseEnd_5237027] using wordTrace_append hprefix tailTrace_5237027
  have hstable : (prefixWord ++ tailWord_5237027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237027).length < 2 ^ (prefixWord ++ tailWord_5237027).sum := by decide
  have hdescent : baseEnd_5237027 < baseStart_5237027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237068 : List Nat := [2, 2, 1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_5237068 : Nat := 118140960795 + 5237068 * 2 ^ 59
def prefixEnd_5237068 : Nat := 4983230072969 + 3 ^ 40 * 5237068 * 2
def baseEnd_5237068 : Nat := 896377701426873727021723

theorem tailTrace_5237068 : CollatzResearch.WordTrace tailWord_5237068 prefixEnd_5237068 896377701426873727021723 := by
  unfold tailWord_5237068
  simp only [CollatzResearch.WordTrace]
  refine ⟨95505781095502265425547929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127341041460669687234063905 95505781095502265425547929)
  ·
    refine ⟨71629335821626699069160947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95505781095502265425547929 71629335821626699069160947)
    ·
      refine ⟨107444003732440048603741421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71629335821626699069160947 107444003732440048603741421)
      ·
        refine ⟨40291501399665018226403033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107444003732440048603741421 40291501399665018226403033)
        ·
          refine ⟨30218626049748763669802275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40291501399665018226403033 30218626049748763669802275)
          ·
            refine ⟨45327939074623145504703413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30218626049748763669802275 45327939074623145504703413)
            ·
              refine ⟨4249494288245919891065945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45327939074623145504703413 4249494288245919891065945)
              ·
                refine ⟨3187120716184439918299459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4249494288245919891065945 3187120716184439918299459)
                ·
                  refine ⟨4780681074276659877449189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3187120716184439918299459 4780681074276659877449189)
                  ·
                    refine ⟨896377701426873727021723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4780681074276659877449189 896377701426873727021723)
                    ·
                      rfl

theorem cell23_5237068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_5237068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237068 prefixEnd_5237068 := by exact prefixLift 5237068
  have htrace : WordTrace (prefixWord ++ tailWord_5237068) baseStart_5237068 baseEnd_5237068 := by
    simpa [prefixWord, tailWord_5237068, baseEnd_5237068] using wordTrace_append hprefix tailTrace_5237068
  have hstable : (prefixWord ++ tailWord_5237068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237068).length < 2 ^ (prefixWord ++ tailWord_5237068).sum := by decide
  have hdescent : baseEnd_5237068 < baseStart_5237068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237107 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 1, 6]
def baseStart_5237107 : Nat := 118140960795 + 5237107 * 2 ^ 59
def prefixEnd_5237107 : Nat := 4983230072969 + 3 ^ 40 * 5237107 * 2
def baseEnd_5237107 : Nat := 896384376675382176159163

theorem tailTrace_5237107 : CollatzResearch.WordTrace tailWord_5237107 prefixEnd_5237107 896384376675382176159163 := by
  unfold tailWord_5237107
  simp only [CollatzResearch.WordTrace]
  refine ⟨191012984637863240511765575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127341989758575493674510383 191012984637863240511765575)
  ·
    refine ⟨286519476956794860767648363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191012984637863240511765575 286519476956794860767648363)
    ·
      refine ⟨429779215435192291151472545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286519476956794860767648363 429779215435192291151472545)
      ·
        refine ⟨322334411576394218363604409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429779215435192291151472545 322334411576394218363604409)
        ·
          refine ⟨241750808682295663772703307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322334411576394218363604409 241750808682295663772703307)
          ·
            refine ⟨362626213023443495659054961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241750808682295663772703307 362626213023443495659054961)
            ·
              refine ⟨271969659767582621744291221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362626213023443495659054961 271969659767582621744291221)
              ·
                refine ⟨12748577801605435394263651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 271969659767582621744291221 12748577801605435394263651)
                ·
                  refine ⟨19122866702408153091395477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12748577801605435394263651 19122866702408153091395477)
                  ·
                    refine ⟨896384376675382176159163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19122866702408153091395477 896384376675382176159163)
                    ·
                      rfl

theorem cell23_5237107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 6].length) (baseStart_5237107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237107 prefixEnd_5237107 := by exact prefixLift 5237107
  have htrace : WordTrace (prefixWord ++ tailWord_5237107) baseStart_5237107 baseEnd_5237107 := by
    simpa [prefixWord, tailWord_5237107, baseEnd_5237107] using wordTrace_append hprefix tailTrace_5237107
  have hstable : (prefixWord ++ tailWord_5237107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237107).length < 2 ^ (prefixWord ++ tailWord_5237107).sum := by decide
  have hdescent : baseEnd_5237107 < baseStart_5237107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237151 : List Nat := [1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 3]
def baseStart_5237151 : Nat := 118140960795 + 5237151 * 2 ^ 59
def prefixEnd_5237151 : Nat := 4983230072969 + 3 ^ 40 * 5237151 * 2
def baseEnd_5237151 : Nat := 2689175723174944356327287

theorem tailTrace_5237151 : CollatzResearch.WordTrace tailWord_5237151 prefixEnd_5237151 2689175723174944356327287 := by
  unfold tailWord_5237151
  simp only [CollatzResearch.WordTrace]
  refine ⟨191014589449703836026367307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127343059633135890684244871 191014589449703836026367307)
  ·
    refine ⟨286521884174555754039550961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191014589449703836026367307 286521884174555754039550961)
    ·
      refine ⟨214891413130916815529663221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286521884174555754039550961 214891413130916815529663221)
      ·
        refine ⟨20146069981023451455905927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214891413130916815529663221 20146069981023451455905927)
        ·
          refine ⟨30219104971535177183858891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20146069981023451455905927 30219104971535177183858891)
          ·
            refine ⟨45328657457302765775788337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30219104971535177183858891 45328657457302765775788337)
            ·
              refine ⟨33996493092977074331841253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45328657457302765775788337 33996493092977074331841253)
              ·
                refine ⟨6374342454933201437220235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33996493092977074331841253 6374342454933201437220235)
                ·
                  refine ⟨9561513682399802155830353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6374342454933201437220235 9561513682399802155830353)
                  ·
                    refine ⟨7171135261799851616872765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9561513682399802155830353 7171135261799851616872765)
                    ·
                      refine ⟨2689175723174944356327287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7171135261799851616872765 2689175723174944356327287)
                      ·
                        rfl

theorem cell23_5237151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_5237151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237151 prefixEnd_5237151 := by exact prefixLift 5237151
  have htrace : WordTrace (prefixWord ++ tailWord_5237151) baseStart_5237151 baseEnd_5237151 := by
    simpa [prefixWord, tailWord_5237151, baseEnd_5237151] using wordTrace_append hprefix tailTrace_5237151
  have hstable : (prefixWord ++ tailWord_5237151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237151).length < 2 ^ (prefixWord ++ tailWord_5237151).sum := by decide
  have hdescent : baseEnd_5237151 < baseStart_5237151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237185 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5237185 : Nat := 118140960795 + 5237185 * 2 ^ 59
def prefixEnd_5237185 : Nat := 4983230072969 + 3 ^ 40 * 5237185 * 2
def baseEnd_5237185 : Nat := 2689193181517197223302131

theorem tailTrace_5237185 : CollatzResearch.WordTrace tailWord_5237185 prefixEnd_5237185 2689193181517197223302131 := by
  unfold tailWord_5237185
  simp only [CollatzResearch.WordTrace]
  refine ⟨191015829531580659833105009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127343886354387106555403339 191015829531580659833105009)
  ·
    refine ⟨143261872148685494874828757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191015829531580659833105009 143261872148685494874828757)
    ·
      refine ⟨3357700128484816286128799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 143261872148685494874828757 3357700128484816286128799)
      ·
        refine ⟨5036550192727224429193199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357700128484816286128799 5036550192727224429193199)
        ·
          refine ⟨7554825289090836643789799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036550192727224429193199 7554825289090836643789799)
          ·
            refine ⟨11332237933636254965684699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7554825289090836643789799 11332237933636254965684699)
            ·
              refine ⟨16998356900454382448527049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11332237933636254965684699 16998356900454382448527049)
              ·
                refine ⟨12748767675340786836395287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16998356900454382448527049 12748767675340786836395287)
                ·
                  refine ⟨19123151513011180254592931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12748767675340786836395287 19123151513011180254592931)
                  ·
                    refine ⟨28684727269516770381889397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19123151513011180254592931 28684727269516770381889397)
                    ·
                      refine ⟨2689193181517197223302131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28684727269516770381889397 2689193181517197223302131)
                      ·
                        rfl

theorem cell23_5237185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5237185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237185 prefixEnd_5237185 := by exact prefixLift 5237185
  have htrace : WordTrace (prefixWord ++ tailWord_5237185) baseStart_5237185 baseEnd_5237185 := by
    simpa [prefixWord, tailWord_5237185, baseEnd_5237185] using wordTrace_append hprefix tailTrace_5237185
  have hstable : (prefixWord ++ tailWord_5237185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237185).length < 2 ^ (prefixWord ++ tailWord_5237185).sum := by decide
  have hdescent : baseEnd_5237185 < baseStart_5237185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237224 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_5237224 : Nat := 118140960795 + 5237224 * 2 ^ 59
def prefixEnd_5237224 : Nat := 4983230072969 + 3 ^ 40 * 5237224 * 2
def baseEnd_5237224 : Nat := 2689213207262722570714451

theorem tailTrace_5237224 : CollatzResearch.WordTrace tailWord_5237224 prefixEnd_5237224 2689213207262722570714451 := by
  unfold tailWord_5237224
  simp only [CollatzResearch.WordTrace]
  refine ⟨95508625989219684746887363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127344834652292912995849817 95508625989219684746887363)
  ·
    refine ⟨143262938983829527120331045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95508625989219684746887363 143262938983829527120331045)
    ·
      refine ⟨26861801059468036335062071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 143262938983829527120331045 26861801059468036335062071)
      ·
        refine ⟨40292701589202054502593107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26861801059468036335062071 40292701589202054502593107)
        ·
          refine ⟨60439052383803081753889661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40292701589202054502593107 60439052383803081753889661)
          ·
            refine ⟨22664644643926155657708623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60439052383803081753889661 22664644643926155657708623)
            ·
              refine ⟨33996966965889233486562935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22664644643926155657708623 33996966965889233486562935)
              ·
                refine ⟨50995450448833850229844403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33996966965889233486562935 50995450448833850229844403)
                ·
                  refine ⟨76493175673250775344766605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50995450448833850229844403 76493175673250775344766605)
                  ·
                    refine ⟨28684940877469040754287477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76493175673250775344766605 28684940877469040754287477)
                    ·
                      refine ⟨2689213207262722570714451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28684940877469040754287477 2689213207262722570714451)
                      ·
                        rfl

theorem cell23_5237224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_5237224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237224 prefixEnd_5237224 := by exact prefixLift 5237224
  have htrace : WordTrace (prefixWord ++ tailWord_5237224) baseStart_5237224 baseEnd_5237224 := by
    simpa [prefixWord, tailWord_5237224, baseEnd_5237224] using wordTrace_append hprefix tailTrace_5237224
  have hstable : (prefixWord ++ tailWord_5237224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237224).length < 2 ^ (prefixWord ++ tailWord_5237224).sum := by decide
  have hdescent : baseEnd_5237224 < baseStart_5237224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237274 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_5237274 : Nat := 118140960795 + 5237274 * 2 ^ 59
def prefixEnd_5237274 : Nat := 4983230072969 + 3 ^ 40 * 5237274 * 2
def baseEnd_5237274 : Nat := 896412960431815791696407

theorem tailTrace_5237274 : CollatzResearch.WordTrace tailWord_5237274 prefixEnd_5237274 896412960431815791696407 := by
  unfold tailWord_5237274
  simp only [CollatzResearch.WordTrace]
  refine ⟨47754768907064557008273719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127346050418838818688729917 47754768907064557008273719)
  ·
    refine ⟨71632153360596835512410579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47754768907064557008273719 71632153360596835512410579)
    ·
      refine ⟨107448230040895253268615869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71632153360596835512410579 107448230040895253268615869)
      ·
        refine ⟨40293086265335719975730951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107448230040895253268615869 40293086265335719975730951)
        ·
          refine ⟨60439629398003579963596427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40293086265335719975730951 60439629398003579963596427)
          ·
            refine ⟨90659444097005369945394641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60439629398003579963596427 90659444097005369945394641)
            ·
              refine ⟨67994583072754027459045981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90659444097005369945394641 67994583072754027459045981)
              ·
                refine ⟨25497968652282760297142243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67994583072754027459045981 25497968652282760297142243)
                ·
                  refine ⟨38246952978424140445713365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25497968652282760297142243 38246952978424140445713365)
                  ·
                    refine ⟨896412960431815791696407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38246952978424140445713365 896412960431815791696407)
                    ·
                      rfl

theorem cell23_5237274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_5237274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237274 prefixEnd_5237274 := by exact prefixLift 5237274
  have htrace : WordTrace (prefixWord ++ tailWord_5237274) baseStart_5237274 baseEnd_5237274 := by
    simpa [prefixWord, tailWord_5237274, baseEnd_5237274] using wordTrace_append hprefix tailTrace_5237274
  have hstable : (prefixWord ++ tailWord_5237274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237274).length < 2 ^ (prefixWord ++ tailWord_5237274).sum := by decide
  have hdescent : baseEnd_5237274 < baseStart_5237274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237325 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_5237325 : Nat := 118140960795 + 5237325 * 2 ^ 59
def prefixEnd_5237325 : Nat := 4983230072969 + 3 ^ 40 * 5237325 * 2
def baseEnd_5237325 : Nat := 896421689602942225183829

theorem tailTrace_5237325 : CollatzResearch.WordTrace tailWord_5237325 prefixEnd_5237325 896421689602942225183829 := by
  unfold tailWord_5237325
  simp only [CollatzResearch.WordTrace]
  refine ⟨191020935751073463743201429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127347290500715642495467619 191020935751073463743201429)
  ·
    refine ⟨8954106363331568612962567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 191020935751073463743201429 8954106363331568612962567)
    ·
      refine ⟨13431159544997352919443851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8954106363331568612962567 13431159544997352919443851)
      ·
        refine ⟨20146739317496029379165777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13431159544997352919443851 20146739317496029379165777)
        ·
          refine ⟨15110054488122022034374333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20146739317496029379165777 15110054488122022034374333)
          ·
            refine ⟨5666270433045758262890375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15110054488122022034374333 5666270433045758262890375)
            ·
              refine ⟨8499405649568637394335563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5666270433045758262890375 8499405649568637394335563)
              ·
                refine ⟨12749108474352956091503345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8499405649568637394335563 12749108474352956091503345)
                ·
                  refine ⟨9561831355764717068627509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12749108474352956091503345 9561831355764717068627509)
                  ·
                    refine ⟨896421689602942225183829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9561831355764717068627509 896421689602942225183829)
                    ·
                      rfl

theorem cell23_5237325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_5237325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237325 prefixEnd_5237325 := by exact prefixLift 5237325
  have htrace : WordTrace (prefixWord ++ tailWord_5237325) baseStart_5237325 baseEnd_5237325 := by
    simpa [prefixWord, tailWord_5237325, baseEnd_5237325] using wordTrace_append hprefix tailTrace_5237325
  have hstable : (prefixWord ++ tailWord_5237325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237325).length < 2 ^ (prefixWord ++ tailWord_5237325).sum := by decide
  have hdescent : baseEnd_5237325 < baseStart_5237325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237448 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_5237448 : Nat := 118140960795 + 5237448 * 2 ^ 59
def prefixEnd_5237448 : Nat := 4983230072969 + 3 ^ 40 * 5237448 * 2
def baseEnd_5237448 : Nat := 2689328226929329694313421

theorem tailTrace_5237448 : CollatzResearch.WordTrace tailWord_5237448 prefixEnd_5237448 2689328226929329694313421 := by
  unfold tailWord_5237448
  simp only [CollatzResearch.WordTrace]
  refine ⟨95512710964813927874964499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127350281286418570499952665 95512710964813927874964499)
  ·
    refine ⟨143269066447220891812446749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95512710964813927874964499 143269066447220891812446749)
    ·
      refine ⟨53725899917707834429667531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143269066447220891812446749 53725899917707834429667531)
      ·
        refine ⟨80588849876561751644501297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53725899917707834429667531 80588849876561751644501297)
        ·
          refine ⟨60441637407421313733375973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80588849876561751644501297 60441637407421313733375973)
          ·
            refine ⟨11332807013891496325007995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60441637407421313733375973 11332807013891496325007995)
            ·
              refine ⟨16999210520837244487511993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11332807013891496325007995 16999210520837244487511993)
              ·
                refine ⟨12749407890627933365633995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16999210520837244487511993 12749407890627933365633995)
                ·
                  refine ⟨19124111835941900048450993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12749407890627933365633995 19124111835941900048450993)
                  ·
                    refine ⟨14343083876956425036338245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19124111835941900048450993 14343083876956425036338245)
                    ·
                      refine ⟨2689328226929329694313421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14343083876956425036338245 2689328226929329694313421)
                      ·
                        rfl

theorem cell23_5237448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_5237448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237448 prefixEnd_5237448 := by exact prefixLift 5237448
  have htrace : WordTrace (prefixWord ++ tailWord_5237448) baseStart_5237448 baseEnd_5237448 := by
    simpa [prefixWord, tailWord_5237448, baseEnd_5237448] using wordTrace_append hprefix tailTrace_5237448
  have hstable : (prefixWord ++ tailWord_5237448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237448).length < 2 ^ (prefixWord ++ tailWord_5237448).sum := by decide
  have hdescent : baseEnd_5237448 < baseStart_5237448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237452 : List Nat := [2, 2, 1, 5, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5237452 : Nat := 118140960795 + 5237452 * 2 ^ 59
def prefixEnd_5237452 : Nat := 4983230072969 + 3 ^ 40 * 5237452 * 2
def baseEnd_5237452 : Nat := 2689330280851947678663403

theorem tailTrace_5237452 : CollatzResearch.WordTrace tailWord_5237452 prefixEnd_5237452 2689330280851947678663403 := by
  unfold tailWord_5237452
  simp only [CollatzResearch.WordTrace]
  refine ⟨95512783910806682216537305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127350378547742242955383073 95512783910806682216537305)
  ·
    refine ⟨71634587933105011662402979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95512783910806682216537305 71634587933105011662402979)
    ·
      refine ⟨107451881899657517493604469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71634587933105011662402979 107451881899657517493604469)
      ·
        refine ⟨10073613928092892265025419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107451881899657517493604469 10073613928092892265025419)
        ·
          refine ⟨15110420892139338397538129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10073613928092892265025419 15110420892139338397538129)
          ·
            refine ⟨11332815669104503798153597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15110420892139338397538129 11332815669104503798153597)
            ·
              refine ⟨4249805875914188924307599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11332815669104503798153597 4249805875914188924307599)
              ·
                refine ⟨6374708813871283386461399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4249805875914188924307599 6374708813871283386461399)
                ·
                  refine ⟨9562063220806925079692099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6374708813871283386461399 9562063220806925079692099)
                  ·
                    refine ⟨14343094831210387619538149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9562063220806925079692099 14343094831210387619538149)
                    ·
                      refine ⟨2689330280851947678663403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14343094831210387619538149 2689330280851947678663403)
                      ·
                        rfl

theorem cell23_5237452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5237452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237452 prefixEnd_5237452 := by exact prefixLift 5237452
  have htrace : WordTrace (prefixWord ++ tailWord_5237452) baseStart_5237452 baseEnd_5237452 := by
    simpa [prefixWord, tailWord_5237452, baseEnd_5237452] using wordTrace_append hprefix tailTrace_5237452
  have hstable : (prefixWord ++ tailWord_5237452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237452).length < 2 ^ (prefixWord ++ tailWord_5237452).sum := by decide
  have hdescent : baseEnd_5237452 < baseStart_5237452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237458 : List Nat := [3, 2, 2, 2, 4, 10]
def baseStart_5237458 : Nat := 118140960795 + 5237458 * 2 ^ 59
def prefixEnd_5237458 : Nat := 4983230072969 + 3 ^ 40 * 5237458 * 2
def baseEnd_5237458 : Nat := 11067215480394545906125

theorem tailTrace_5237458 : CollatzResearch.WordTrace tailWord_5237458 prefixEnd_5237458 11067215480394545906125 := by
  unfold tailWord_5237458
  simp only [CollatzResearch.WordTrace]
  refine ⟨47756446664897906864448257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127350524439727751638528685 47756446664897906864448257)
  ·
    refine ⟨35817334998673430148336193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47756446664897906864448257 35817334998673430148336193)
    ·
      refine ⟨26863001249005072611252145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35817334998673430148336193 26863001249005072611252145)
      ·
        refine ⟨20147250936753804458439109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26863001249005072611252145 20147250936753804458439109)
        ·
          refine ⟨3777609550641338335957333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20147250936753804458439109 3777609550641338335957333)
          ·
            refine ⟨11067215480394545906125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3777609550641338335957333 11067215480394545906125)
            ·
              rfl

theorem cell23_5237458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 10].length) (baseStart_5237458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237458 prefixEnd_5237458 := by exact prefixLift 5237458
  have htrace : WordTrace (prefixWord ++ tailWord_5237458) baseStart_5237458 baseEnd_5237458 := by
    simpa [prefixWord, tailWord_5237458, baseEnd_5237458] using wordTrace_append hprefix tailTrace_5237458
  have hstable : (prefixWord ++ tailWord_5237458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237458).length < 2 ^ (prefixWord ++ tailWord_5237458).sum := by decide
  have hdescent : baseEnd_5237458 < baseStart_5237458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237471 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 2, 7]
def baseStart_5237471 : Nat := 118140960795 + 5237471 * 2 ^ 59
def prefixEnd_5237471 : Nat := 4983230072969 + 3 ^ 40 * 5237471 * 2
def baseEnd_5237471 : Nat := 896446678994794368108605

theorem tailTrace_5237471 : CollatzResearch.WordTrace tailWord_5237471 prefixEnd_5237471 896446678994794368108605 := by
  unfold tailWord_5237471
  simp only [CollatzResearch.WordTrace]
  refine ⟨191026260808544530678016267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127350840539029687118677511 191026260808544530678016267)
  ·
    refine ⟨286539391212816796017024401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191026260808544530678016267 286539391212816796017024401)
    ·
      refine ⟨214904543409612597012768301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286539391212816796017024401 214904543409612597012768301)
      ·
        refine ⟨80589203778604723879788113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214904543409612597012768301 80589203778604723879788113)
        ·
          refine ⟨60441902833953542909841085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80589203778604723879788113 60441902833953542909841085)
          ·
            refine ⟨22665713562732578591190407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60441902833953542909841085 22665713562732578591190407)
            ·
              refine ⟨33998570344098867886785611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22665713562732578591190407 33998570344098867886785611)
              ·
                refine ⟨50997855516148301830178417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33998570344098867886785611 50997855516148301830178417)
                ·
                  refine ⟨38248391637111226372633813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50997855516148301830178417 38248391637111226372633813)
                  ·
                    refine ⟨896446678994794368108605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38248391637111226372633813 896446678994794368108605)
                    ·
                      rfl

theorem cell23_5237471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_5237471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237471 prefixEnd_5237471 := by exact prefixLift 5237471
  have htrace : WordTrace (prefixWord ++ tailWord_5237471) baseStart_5237471 baseEnd_5237471 := by
    simpa [prefixWord, tailWord_5237471, baseEnd_5237471] using wordTrace_append hprefix tailTrace_5237471
  have hstable : (prefixWord ++ tailWord_5237471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237471).length < 2 ^ (prefixWord ++ tailWord_5237471).sum := by decide
  have hdescent : baseEnd_5237471 < baseStart_5237471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237485 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_5237485 : Nat := 118140960795 + 5237485 * 2 ^ 59
def prefixEnd_5237485 : Nat := 4983230072969 + 3 ^ 40 * 5237485 * 2
def baseEnd_5237485 : Nat := 2689347225713546049550751

theorem tailTrace_5237485 : CollatzResearch.WordTrace tailWord_5237485 prefixEnd_5237485 2689347225713546049550751 := by
  unfold tailWord_5237485
  simp only [CollatzResearch.WordTrace]
  refine ⟨191026771430493811069025909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127351180953662540712683939 191026771430493811069025909)
  ·
    refine ⟨17908759821608794787721179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191026771430493811069025909 17908759821608794787721179)
    ·
      refine ⟨26863139732413192181581769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17908759821608794787721179 26863139732413192181581769)
      ·
        refine ⟨20147354799309894136186327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26863139732413192181581769 20147354799309894136186327)
        ·
          refine ⟨30221032198964841204279491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20147354799309894136186327 30221032198964841204279491)
          ·
            refine ⟨45331548298447261806419237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30221032198964841204279491 45331548298447261806419237)
            ·
              refine ⟨8499665305958861588703607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45331548298447261806419237 8499665305958861588703607)
              ·
                refine ⟨12749497958938292383055411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8499665305958861588703607 12749497958938292383055411)
                ·
                  refine ⟨19124246938407438574583117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12749497958938292383055411 19124246938407438574583117)
                  ·
                    refine ⟨7171592601902789465468669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19124246938407438574583117 7171592601902789465468669)
                    ·
                      refine ⟨2689347225713546049550751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7171592601902789465468669 2689347225713546049550751)
                      ·
                        rfl

theorem cell23_5237485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_5237485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237485 prefixEnd_5237485 := by exact prefixLift 5237485
  have htrace : WordTrace (prefixWord ++ tailWord_5237485) baseStart_5237485 baseEnd_5237485 := by
    simpa [prefixWord, tailWord_5237485, baseEnd_5237485] using wordTrace_append hprefix tailTrace_5237485
  have hstable : (prefixWord ++ tailWord_5237485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237485).length < 2 ^ (prefixWord ++ tailWord_5237485).sum := by decide
  have hdescent : baseEnd_5237485 < baseStart_5237485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237491 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 4]
def baseStart_5237491 : Nat := 118140960795 + 5237491 * 2 ^ 59
def prefixEnd_5237491 : Nat := 4983230072969 + 3 ^ 40 * 5237491 * 2
def baseEnd_5237491 : Nat := 2689350306597473026075723

theorem tailTrace_5237491 : CollatzResearch.WordTrace tailWord_5237491 prefixEnd_5237491 2689350306597473026075723 := by
  unfold tailWord_5237491
  simp only [CollatzResearch.WordTrace]
  refine ⟨191026990268472074093744327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127351326845648049395829551 191026990268472074093744327)
  ·
    refine ⟨286540485402708111140616491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191026990268472074093744327 286540485402708111140616491)
    ·
      refine ⟨429810728104062166710924737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286540485402708111140616491 429810728104062166710924737)
      ·
        refine ⟨322358046078046625033193553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429810728104062166710924737 322358046078046625033193553)
        ·
          refine ⟨241768534558534968774895165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322358046078046625033193553 241768534558534968774895165)
          ·
            refine ⟨90663200459450613290585687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241768534558534968774895165 90663200459450613290585687)
            ·
              refine ⟨135994800689175919935878531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90663200459450613290585687 135994800689175919935878531)
              ·
                refine ⟨203992201033763879903817797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135994800689175919935878531 203992201033763879903817797)
                ·
                  refine ⟨38248537693830727481965837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203992201033763879903817797 38248537693830727481965837)
                  ·
                    refine ⟨14343201635186522805737189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38248537693830727481965837 14343201635186522805737189)
                    ·
                      refine ⟨2689350306597473026075723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14343201635186522805737189 2689350306597473026075723)
                      ·
                        rfl

theorem cell23_5237491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_5237491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237491 prefixEnd_5237491 := by exact prefixLift 5237491
  have htrace : WordTrace (prefixWord ++ tailWord_5237491) baseStart_5237491 baseEnd_5237491 := by
    simpa [prefixWord, tailWord_5237491, baseEnd_5237491] using wordTrace_append hprefix tailTrace_5237491
  have hstable : (prefixWord ++ tailWord_5237491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237491).length < 2 ^ (prefixWord ++ tailWord_5237491).sum := by decide
  have hdescent : baseEnd_5237491 < baseStart_5237491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237495 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 1, 3, 2]
def baseStart_5237495 : Nat := 118140960795 + 5237495 * 2 ^ 59
def prefixEnd_5237495 : Nat := 4983230072969 + 3 ^ 40 * 5237495 * 2
def baseEnd_5237495 : Nat := 2689352360520091010425705

theorem tailTrace_5237495 : CollatzResearch.WordTrace tailWord_5237495 prefixEnd_5237495 2689352360520091010425705 := by
  unfold tailWord_5237495
  simp only [CollatzResearch.WordTrace]
  refine ⟨191027136160457582776889939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127351424106971721851259959 191027136160457582776889939)
  ·
    refine ⟨286540704240686374165334909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191027136160457582776889939 286540704240686374165334909)
    ·
      refine ⟨107452764090257390312000591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 286540704240686374165334909 107452764090257390312000591)
      ·
        refine ⟨161179146135386085468000887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107452764090257390312000591 161179146135386085468000887)
        ·
          refine ⟨241768719203079128202001331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161179146135386085468000887 241768719203079128202001331)
          ·
            refine ⟨362653078804618692303001997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241768719203079128202001331 362653078804618692303001997)
            ·
              refine ⟨135994904551732009613625749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362653078804618692303001997 135994904551732009613625749)
              ·
                refine ⟨6374761150862437950638707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135994904551732009613625749 6374761150862437950638707)
                ·
                  refine ⟨9562141726293656925958061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6374761150862437950638707 9562141726293656925958061)
                  ·
                    refine ⟨3585803147360121347234273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9562141726293656925958061 3585803147360121347234273)
                    ·
                      refine ⟨2689352360520091010425705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585803147360121347234273 2689352360520091010425705)
                      ·
                        rfl

theorem cell23_5237495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_5237495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237495 prefixEnd_5237495 := by exact prefixLift 5237495
  have htrace : WordTrace (prefixWord ++ tailWord_5237495) baseStart_5237495 baseEnd_5237495 := by
    simpa [prefixWord, tailWord_5237495, baseEnd_5237495] using wordTrace_append hprefix tailTrace_5237495
  have hstable : (prefixWord ++ tailWord_5237495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237495).length < 2 ^ (prefixWord ++ tailWord_5237495).sum := by decide
  have hdescent : baseEnd_5237495 < baseStart_5237495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237501 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_5237501 : Nat := 118140960795 + 5237501 * 2 ^ 59
def prefixEnd_5237501 : Nat := 4983230072969 + 3 ^ 40 * 5237501 * 2
def baseEnd_5237501 : Nat := 896451813801339328983559

theorem tailTrace_5237501 : CollatzResearch.WordTrace tailWord_5237501 prefixEnd_5237501 896451813801339328983559 := by
  unfold tailWord_5237501
  simp only [CollatzResearch.WordTrace]
  refine ⟨191027354998435845801608357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127351569998957230534405571 191027354998435845801608357)
  ·
    refine ⟨35817629062206721087801567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191027354998435845801608357 35817629062206721087801567)
    ·
      refine ⟨53726443593310081631702351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35817629062206721087801567 53726443593310081631702351)
      ·
        refine ⟨80589665389965122447553527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53726443593310081631702351 80589665389965122447553527)
        ·
          refine ⟨120884498084947683671330291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80589665389965122447553527 120884498084947683671330291)
          ·
            refine ⟨181326747127421525506995437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120884498084947683671330291 181326747127421525506995437)
            ·
              refine ⟨67997530172783072065123289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181326747127421525506995437 67997530172783072065123289)
              ·
                refine ⟨50998147629587304048842467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67997530172783072065123289 50998147629587304048842467)
                ·
                  refine ⟨76497221444380956073263701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50998147629587304048842467 76497221444380956073263701)
                  ·
                    refine ⟨896451813801339328983559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76497221444380956073263701 896451813801339328983559)
                    ·
                      rfl

theorem cell23_5237501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_5237501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237501 prefixEnd_5237501 := by exact prefixLift 5237501
  have htrace : WordTrace (prefixWord ++ tailWord_5237501) baseStart_5237501 baseEnd_5237501 := by
    simpa [prefixWord, tailWord_5237501, baseEnd_5237501] using wordTrace_append hprefix tailTrace_5237501
  have hstable : (prefixWord ++ tailWord_5237501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237501).length < 2 ^ (prefixWord ++ tailWord_5237501).sum := by decide
  have hdescent : baseEnd_5237501 < baseStart_5237501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237512 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_5237512 : Nat := 118140960795 + 5237512 * 2 ^ 59
def prefixEnd_5237512 : Nat := 4983230072969 + 3 ^ 40 * 5237512 * 2
def baseEnd_5237512 : Nat := 2689361089691217443913127

theorem tailTrace_5237512 : CollatzResearch.WordTrace tailWord_5237512 prefixEnd_5237512 2689361089691217443913127 := by
  unfold tailWord_5237512
  simp only [CollatzResearch.WordTrace]
  refine ⟨95513878100697997340129395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127351837467597329786839193 95513878100697997340129395)
  ·
    refine ⟨143270817151046996010194093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95513878100697997340129395 143270817151046996010194093)
    ·
      refine ⟨53726556431642623503822785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 143270817151046996010194093 53726556431642623503822785)
      ·
        refine ⟨40294917323731967627867089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53726556431642623503822785 40294917323731967627867089)
        ·
          refine ⟨30221187992798975720900317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40294917323731967627867089 30221187992798975720900317)
          ·
            refine ⟨11332945497299615895337619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30221187992798975720900317 11332945497299615895337619)
            ·
              refine ⟨16999418245949423843006429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11332945497299615895337619 16999418245949423843006429)
              ·
                refine ⟨6374781842231033941127411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16999418245949423843006429 6374781842231033941127411)
                ·
                  refine ⟨9562172763346550911691117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6374781842231033941127411 9562172763346550911691117)
                  ·
                    refine ⟨3585814786254956591884169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9562172763346550911691117 3585814786254956591884169)
                    ·
                      refine ⟨2689361089691217443913127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585814786254956591884169 2689361089691217443913127)
                      ·
                        rfl

theorem cell23_5237512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_5237512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237512 prefixEnd_5237512 := by exact prefixLift 5237512
  have htrace : WordTrace (prefixWord ++ tailWord_5237512) baseStart_5237512 baseEnd_5237512 := by
    simpa [prefixWord, tailWord_5237512, baseEnd_5237512] using wordTrace_append hprefix tailTrace_5237512
  have hstable : (prefixWord ++ tailWord_5237512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237512).length < 2 ^ (prefixWord ++ tailWord_5237512).sum := by decide
  have hdescent : baseEnd_5237512 < baseStart_5237512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237546 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5237546 : Nat := 118140960795 + 5237546 * 2 ^ 59
def prefixEnd_5237546 : Nat := 4983230072969 + 3 ^ 40 * 5237546 * 2
def baseEnd_5237546 : Nat := 2689378548033470310887971

theorem tailTrace_5237546 : CollatzResearch.WordTrace tailWord_5237546 prefixEnd_5237546 2689378548033470310887971 := by
  unfold tailWord_5237546
  simp only [CollatzResearch.WordTrace]
  refine ⟨47757249070818204621749123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127352664188848545657997661 47757249070818204621749123)
  ·
    refine ⟨71635873606227306932623685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47757249070818204621749123 71635873606227306932623685)
    ·
      refine ⟨13431726301167620049866941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71635873606227306932623685 13431726301167620049866941)
      ·
        refine ⟨5036897362937857518700103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13431726301167620049866941 5036897362937857518700103)
        ·
          refine ⟨7555346044406786278050155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036897362937857518700103 7555346044406786278050155)
          ·
            refine ⟨11333019066610179417075233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7555346044406786278050155 11333019066610179417075233)
            ·
              refine ⟨8499764299957634562806425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11333019066610179417075233 8499764299957634562806425)
              ·
                refine ⟨6374823224968225922104819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8499764299957634562806425 6374823224968225922104819)
                ·
                  refine ⟨9562234837452338883157229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6374823224968225922104819 9562234837452338883157229)
                  ·
                    refine ⟨3585838064044627081183961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9562234837452338883157229 3585838064044627081183961)
                    ·
                      refine ⟨2689378548033470310887971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585838064044627081183961 2689378548033470310887971)
                      ·
                        rfl

theorem cell23_5237546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5237546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237546 prefixEnd_5237546 := by exact prefixLift 5237546
  have htrace : WordTrace (prefixWord ++ tailWord_5237546) baseStart_5237546 baseEnd_5237546 := by
    simpa [prefixWord, tailWord_5237546, baseEnd_5237546] using wordTrace_append hprefix tailTrace_5237546
  have hstable : (prefixWord ++ tailWord_5237546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237546).length < 2 ^ (prefixWord ++ tailWord_5237546).sum := by decide
  have hdescent : baseEnd_5237546 < baseStart_5237546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237635 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 3]
def baseStart_5237635 : Nat := 118140960795 + 5237635 * 2 ^ 59
def prefixEnd_5237635 : Nat := 4983230072969 + 3 ^ 40 * 5237635 * 2
def baseEnd_5237635 : Nat := 2689424247811720462675061

theorem tailTrace_5237635 : CollatzResearch.WordTrace tailWord_5237635 prefixEnd_5237635 2689424247811720462675061 := by
  unfold tailWord_5237635
  simp only [CollatzResearch.WordTrace]
  refine ⟨191032242379950386686986359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127354828253300257791324239 191032242379950386686986359)
  ·
    refine ⟨286548363569925580030479539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191032242379950386686986359 286548363569925580030479539)
    ·
      refine ⟨429822545354888370045719309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286548363569925580030479539 429822545354888370045719309)
      ·
        refine ⟨161183454508083138767144741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 429822545354888370045719309 161183454508083138767144741)
        ·
          refine ⟨30221897720265588518839639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161183454508083138767144741 30221897720265588518839639)
          ·
            refine ⟨45332846580398382778259459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30221897720265588518839639 45332846580398382778259459)
            ·
              refine ⟨67999269870597574167389189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45332846580398382778259459 67999269870597574167389189)
              ·
                refine ⟨12749863100737045156385473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67999269870597574167389189 12749863100737045156385473)
                ·
                  refine ⟨9562397325552783867289105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12749863100737045156385473 9562397325552783867289105)
                  ·
                    refine ⟨7171797994164587900466829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9562397325552783867289105 7171797994164587900466829)
                    ·
                      refine ⟨2689424247811720462675061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7171797994164587900466829 2689424247811720462675061)
                      ·
                        rfl

theorem cell23_5237635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_5237635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237635 prefixEnd_5237635 := by exact prefixLift 5237635
  have htrace : WordTrace (prefixWord ++ tailWord_5237635) baseStart_5237635 baseEnd_5237635 := by
    simpa [prefixWord, tailWord_5237635, baseEnd_5237635] using wordTrace_append hprefix tailTrace_5237635
  have hstable : (prefixWord ++ tailWord_5237635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237635).length < 2 ^ (prefixWord ++ tailWord_5237635).sum := by decide
  have hdescent : baseEnd_5237635 < baseStart_5237635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237675 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 1, 5, 2]
def baseStart_5237675 : Nat := 118140960795 + 5237675 * 2 ^ 59
def prefixEnd_5237675 : Nat := 4983230072969 + 3 ^ 40 * 5237675 * 2
def baseEnd_5237675 : Nat := 2689444787037900306174877

theorem tailTrace_5237675 : CollatzResearch.WordTrace tailWord_5237675 prefixEnd_5237675 2689444787037900306174877 := by
  unfold tailWord_5237675
  simp only [CollatzResearch.WordTrace]
  refine ⟨191033701299805473518442479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127355800866536982345628319 191033701299805473518442479)
  ·
    refine ⟨286550551949708210277663719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191033701299805473518442479 286550551949708210277663719)
    ·
      refine ⟨429825827924562315416495579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286550551949708210277663719 429825827924562315416495579)
      ·
        refine ⟨644738741886843473124743369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429825827924562315416495579 644738741886843473124743369)
        ·
          refine ⟨483554056415132604843557527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644738741886843473124743369 483554056415132604843557527)
          ·
            refine ⟨725331084622698907265336291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483554056415132604843557527 725331084622698907265336291)
            ·
              refine ⟨1087996626934048360898004437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725331084622698907265336291 1087996626934048360898004437)
              ·
                refine ⟨25499920943766758458546979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1087996626934048360898004437 25499920943766758458546979)
                ·
                  refine ⟨38249881415650137687820469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25499920943766758458546979 38249881415650137687820469)
                  ·
                    refine ⟨3585926382717200408233169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38249881415650137687820469 3585926382717200408233169)
                    ·
                      refine ⟨2689444787037900306174877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585926382717200408233169 2689444787037900306174877)
                      ·
                        rfl

theorem cell23_5237675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 5, 2].length) (baseStart_5237675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237675 prefixEnd_5237675 := by exact prefixLift 5237675
  have htrace : WordTrace (prefixWord ++ tailWord_5237675) baseStart_5237675 baseEnd_5237675 := by
    simpa [prefixWord, tailWord_5237675, baseEnd_5237675] using wordTrace_append hprefix tailTrace_5237675
  have hstable : (prefixWord ++ tailWord_5237675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237675).length < 2 ^ (prefixWord ++ tailWord_5237675).sum := by decide
  have hdescent : baseEnd_5237675 < baseStart_5237675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237705 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 4, 6, 2]
def baseStart_5237705 : Nat := 118140960795 + 5237705 * 2 ^ 59
def prefixEnd_5237705 : Nat := 4983230072969 + 3 ^ 40 * 5237705 * 2
def baseEnd_5237705 : Nat := 2689460191457535188799739

theorem tailTrace_5237705 : CollatzResearch.WordTrace tailWord_5237705 prefixEnd_5237705 2689460191457535188799739 := by
  unfold tailWord_5237705
  simp only [CollatzResearch.WordTrace]
  refine ⟨191034795489696788642034569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127356530326464525761356379 191034795489696788642034569)
  ·
    refine ⟨143276096617272591481525927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191034795489696788642034569 143276096617272591481525927)
    ·
      refine ⟨214914144925908887222288891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143276096617272591481525927 214914144925908887222288891)
      ·
        refine ⟨322371217388863330833433337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214914144925908887222288891 322371217388863330833433337)
        ·
          refine ⟨241778413041647498125075003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322371217388863330833433337 241778413041647498125075003)
          ·
            refine ⟨362667619562471247187612505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241778413041647498125075003 362667619562471247187612505)
            ·
              refine ⟨272000714671853435390709379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362667619562471247187612505 272000714671853435390709379)
              ·
                refine ⟨408001072007780153086064069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272000714671853435390709379 408001072007780153086064069)
                ·
                  refine ⟨76500201001458778703637013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408001072007780153086064069 76500201001458778703637013)
                  ·
                    refine ⟨3585946921943380251732985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76500201001458778703637013 3585946921943380251732985)
                    ·
                      refine ⟨2689460191457535188799739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585946921943380251732985 2689460191457535188799739)
                      ·
                        rfl

theorem cell23_5237705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 6, 2].length) (baseStart_5237705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237705 prefixEnd_5237705 := by exact prefixLift 5237705
  have htrace : WordTrace (prefixWord ++ tailWord_5237705) baseStart_5237705 baseEnd_5237705 := by
    simpa [prefixWord, tailWord_5237705, baseEnd_5237705] using wordTrace_append hprefix tailTrace_5237705
  have hstable : (prefixWord ++ tailWord_5237705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237705).length < 2 ^ (prefixWord ++ tailWord_5237705).sum := by decide
  have hdescent : baseEnd_5237705 < baseStart_5237705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237722 : List Nat := [3, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4]
def baseStart_5237722 : Nat := 118140960795 + 5237722 * 2 ^ 59
def prefixEnd_5237722 : Nat := 4983230072969 + 3 ^ 40 * 5237722 * 2
def baseEnd_5237722 : Nat := 2689468920628661622287161

theorem tailTrace_5237722 : CollatzResearch.WordTrace tailWord_5237722 prefixEnd_5237722 2689468920628661622287161 := by
  unfold tailWord_5237722
  simp only [CollatzResearch.WordTrace]
  refine ⟨47758853882658800136350855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127356943687090133696935613 47758853882658800136350855)
  ·
    refine ⟨71638280823988200204526283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47758853882658800136350855 71638280823988200204526283)
    ·
      refine ⟨107457421235982300306789425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71638280823988200204526283 107457421235982300306789425)
      ·
        refine ⟨80593065926986725230092069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107457421235982300306789425 80593065926986725230092069)
        ·
          refine ⟨15111199861310010980642263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80593065926986725230092069 15111199861310010980642263)
          ·
            refine ⟨22666799791965016470963395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15111199861310010980642263 22666799791965016470963395)
            ·
              refine ⟨34000199687947524706445093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22666799791965016470963395 34000199687947524706445093)
              ·
                refine ⟨6375037441490160882458455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34000199687947524706445093 6375037441490160882458455)
                ·
                  refine ⟨9562556162235241323687683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6375037441490160882458455 9562556162235241323687683)
                  ·
                    refine ⟨14343834243352861985531525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9562556162235241323687683 14343834243352861985531525)
                    ·
                      refine ⟨2689468920628661622287161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14343834243352861985531525 2689468920628661622287161)
                      ·
                        rfl

theorem cell23_5237722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_5237722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237722 prefixEnd_5237722 := by exact prefixLift 5237722
  have htrace : WordTrace (prefixWord ++ tailWord_5237722) baseStart_5237722 baseEnd_5237722 := by
    simpa [prefixWord, tailWord_5237722, baseEnd_5237722] using wordTrace_append hprefix tailTrace_5237722
  have hstable : (prefixWord ++ tailWord_5237722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237722).length < 2 ^ (prefixWord ++ tailWord_5237722).sum := by decide
  have hdescent : baseEnd_5237722 < baseStart_5237722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237745 : List Nat := [1, 2, 2, 2, 4, 3, 9]
def baseStart_5237745 : Nat := 118140960795 + 5237745 * 2 ^ 59
def prefixEnd_5237745 : Nat := 4983230072969 + 3 ^ 40 * 5237745 * 2
def baseEnd_5237745 : Nat := 33203465810910062127155

theorem tailTrace_5237745 : CollatzResearch.WordTrace tailWord_5237745 prefixEnd_5237745 33203465810910062127155 := by
  unfold tailWord_5237745
  simp only [CollatzResearch.WordTrace]
  refine ⟨191036254409551875473490689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127357502939701250315660459 191036254409551875473490689)
  ·
    refine ⟨143277190807163906605118017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191036254409551875473490689 143277190807163906605118017)
    ·
      refine ⟨107457893105372929953838513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143277190807163906605118017 107457893105372929953838513)
      ·
        refine ⟨80593419829029697465378885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107457893105372929953838513 80593419829029697465378885)
        ·
          refine ⟨15111266217943068274758541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80593419829029697465378885 15111266217943068274758541)
          ·
            refine ⟨5666724831728650603034453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15111266217943068274758541 5666724831728650603034453)
            ·
              refine ⟨33203465810910062127155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5666724831728650603034453 33203465810910062127155)
              ·
                rfl

theorem cell23_5237745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 9].length) (baseStart_5237745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237745 prefixEnd_5237745 := by exact prefixLift 5237745
  have htrace : WordTrace (prefixWord ++ tailWord_5237745) baseStart_5237745 baseEnd_5237745 := by
    simpa [prefixWord, tailWord_5237745, baseEnd_5237745] using wordTrace_append hprefix tailTrace_5237745
  have hstable : (prefixWord ++ tailWord_5237745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237745).length < 2 ^ (prefixWord ++ tailWord_5237745).sum := by decide
  have hdescent : baseEnd_5237745 < baseStart_5237745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237756 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_5237756 : Nat := 118140960795 + 5237756 * 2 ^ 59
def prefixEnd_5237756 : Nat := 4983230072969 + 3 ^ 40 * 5237756 * 2
def baseEnd_5237756 : Nat := 2689486378970914489262005

theorem tailTrace_5237756 : CollatzResearch.WordTrace tailWord_5237756 prefixEnd_5237756 2689486378970914489262005 := by
  unfold tailWord_5237756
  simp only [CollatzResearch.WordTrace]
  refine ⟨95518327806256012176070561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127357770408341349568094081 95518327806256012176070561)
  ·
    refine ⟨71638745854692009132052921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95518327806256012176070561 71638745854692009132052921)
    ·
      refine ⟨53729059391019006849039691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71638745854692009132052921 53729059391019006849039691)
      ·
        refine ⟨80593589086528510273559537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53729059391019006849039691 80593589086528510273559537)
        ·
          refine ⟨60445191814896382705169653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80593589086528510273559537 60445191814896382705169653)
          ·
            refine ⟨5666736732646535878609655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60445191814896382705169653 5666736732646535878609655)
            ·
              refine ⟨8500105098969803817914483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5666736732646535878609655 8500105098969803817914483)
              ·
                refine ⟨12750157648454705726871725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8500105098969803817914483 12750157648454705726871725)
                ·
                  refine ⟨4781309118170514647576897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12750157648454705726871725 4781309118170514647576897)
                  ·
                    refine ⟨3585981838627885985682673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4781309118170514647576897 3585981838627885985682673)
                    ·
                      refine ⟨2689486378970914489262005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3585981838627885985682673 2689486378970914489262005)
                      ·
                        rfl

theorem cell23_5237756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_5237756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237756 prefixEnd_5237756 := by exact prefixLift 5237756
  have htrace : WordTrace (prefixWord ++ tailWord_5237756) baseStart_5237756 baseEnd_5237756 := by
    simpa [prefixWord, tailWord_5237756, baseEnd_5237756] using wordTrace_append hprefix tailTrace_5237756
  have hstable : (prefixWord ++ tailWord_5237756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237756).length < 2 ^ (prefixWord ++ tailWord_5237756).sum := by decide
  have hdescent : baseEnd_5237756 < baseStart_5237756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237789 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_5237789 : Nat := 118140960795 + 5237789 * 2 ^ 59
def prefixEnd_5237789 : Nat := 4983230072969 + 3 ^ 40 * 5237789 * 2
def baseEnd_5237789 : Nat := 2689503323832512860149353

theorem tailTrace_5237789 : CollatzResearch.WordTrace tailWord_5237789 prefixEnd_5237789 2689503323832512860149353 := by
  unfold tailWord_5237789
  simp only [CollatzResearch.WordTrace]
  refine ⟨191037859221392470988092421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127358572814261647325394947 191037859221392470988092421)
  ·
    refine ⟨35819598604011088310267329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 191037859221392470988092421 35819598604011088310267329)
    ·
      refine ⟨26864698953008316232700497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35819598604011088310267329 26864698953008316232700497)
      ·
        refine ⟨20148524214756237174525373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26864698953008316232700497 20148524214756237174525373)
        ·
          refine ⟨7555696580533588940447015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20148524214756237174525373 7555696580533588940447015)
          ·
            refine ⟨11333544870800383410670523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7555696580533588940447015 11333544870800383410670523)
            ·
              refine ⟨17000317306200575116005785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11333544870800383410670523 17000317306200575116005785)
              ·
                refine ⟨12750237979650431337004339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17000317306200575116005785 12750237979650431337004339)
                ·
                  refine ⟨19125356969475647005506509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12750237979650431337004339 19125356969475647005506509)
                  ·
                    refine ⟨7172008863553367627064941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19125356969475647005506509 7172008863553367627064941)
                    ·
                      refine ⟨2689503323832512860149353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7172008863553367627064941 2689503323832512860149353)
                      ·
                        rfl

theorem cell23_5237789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_5237789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237789 prefixEnd_5237789 := by exact prefixLift 5237789
  have htrace : WordTrace (prefixWord ++ tailWord_5237789) baseStart_5237789 baseEnd_5237789 := by
    simpa [prefixWord, tailWord_5237789, baseEnd_5237789] using wordTrace_append hprefix tailTrace_5237789
  have hstable : (prefixWord ++ tailWord_5237789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237789).length < 2 ^ (prefixWord ++ tailWord_5237789).sum := by decide
  have hdescent : baseEnd_5237789 < baseStart_5237789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237806 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_5237806 : Nat := 118140960795 + 5237806 * 2 ^ 59
def prefixEnd_5237806 : Nat := 4983230072969 + 3 ^ 40 * 5237806 * 2
def baseEnd_5237806 : Nat := 2689512053003639293636775

theorem tailTrace_5237806 : CollatzResearch.WordTrace tailWord_5237806 prefixEnd_5237806 2689512053003639293636775 := by
  unfold tailWord_5237806
  simp only [CollatzResearch.WordTrace]
  refine ⟨23879809907791360361432659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127358986174887255260974181 23879809907791360361432659)
  ·
    refine ⟨35819714861687040542148989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23879809907791360361432659 35819714861687040542148989)
    ·
      refine ⟨13432393073132640203305871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35819714861687040542148989 13432393073132640203305871)
      ·
        refine ⟨20148589609698960304958807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13432393073132640203305871 20148589609698960304958807)
        ·
          refine ⟨30222884414548440457438211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20148589609698960304958807 30222884414548440457438211)
          ·
            refine ⟨45334326621822660686157317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30222884414548440457438211 45334326621822660686157317)
            ·
              refine ⟨8500186241591748878654497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45334326621822660686157317 8500186241591748878654497)
              ·
                refine ⟨6375139681193811658990873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8500186241591748878654497 6375139681193811658990873)
                ·
                  refine ⟨4781354760895358744243155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6375139681193811658990873 4781354760895358744243155)
                  ·
                    refine ⟨7172032141343038116364733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4781354760895358744243155 7172032141343038116364733)
                    ·
                      refine ⟨2689512053003639293636775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7172032141343038116364733 2689512053003639293636775)
                      ·
                        rfl

theorem cell23_5237806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_5237806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237806 prefixEnd_5237806 := by exact prefixLift 5237806
  have htrace : WordTrace (prefixWord ++ tailWord_5237806) baseStart_5237806 baseEnd_5237806 := by
    simpa [prefixWord, tailWord_5237806, baseEnd_5237806] using wordTrace_append hprefix tailTrace_5237806
  have hstable : (prefixWord ++ tailWord_5237806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237806).length < 2 ^ (prefixWord ++ tailWord_5237806).sum := by decide
  have hdescent : baseEnd_5237806 < baseStart_5237806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237822 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_5237822 : Nat := 118140960795 + 5237822 * 2 ^ 59
def prefixEnd_5237822 : Nat := 4983230072969 + 3 ^ 40 * 5237822 * 2
def baseEnd_5237822 : Nat := 896506756231370410345567

theorem tailTrace_5237822 : CollatzResearch.WordTrace tailWord_5237822 prefixEnd_5237822 896506756231370410345567 := by
  unfold tailWord_5237822
  simp only [CollatzResearch.WordTrace]
  refine ⟨23879882853784114703005465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127359375220181945082695813 23879882853784114703005465)
  ·
    refine ⟨17909912140338086027254099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23879882853784114703005465 17909912140338086027254099)
    ·
      refine ⟨26864868210507129040881149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17909912140338086027254099 26864868210507129040881149)
      ·
        refine ⟨10074325578940173390330431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26864868210507129040881149 10074325578940173390330431)
        ·
          refine ⟨15111488368410260085495647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10074325578940173390330431 15111488368410260085495647)
          ·
            refine ⟨22667232552615390128243471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15111488368410260085495647 22667232552615390128243471)
            ·
              refine ⟨34000848828923085192365207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22667232552615390128243471 34000848828923085192365207)
              ·
                refine ⟨51001273243384627788547811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34000848828923085192365207 51001273243384627788547811)
                ·
                  refine ⟨76501909865076941682821717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51001273243384627788547811 76501909865076941682821717)
                  ·
                    refine ⟨896506756231370410345567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76501909865076941682821717 896506756231370410345567)
                    ·
                      rfl

theorem cell23_5237822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_5237822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237822 prefixEnd_5237822 := by exact prefixLift 5237822
  have htrace : WordTrace (prefixWord ++ tailWord_5237822) baseStart_5237822 baseEnd_5237822 := by
    simpa [prefixWord, tailWord_5237822, baseEnd_5237822] using wordTrace_append hprefix tailTrace_5237822
  have hstable : (prefixWord ++ tailWord_5237822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237822).length < 2 ^ (prefixWord ++ tailWord_5237822).sum := by decide
  have hdescent : baseEnd_5237822 < baseStart_5237822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237863 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_5237863 : Nat := 118140960795 + 5237863 * 2 ^ 59
def prefixEnd_5237863 : Nat := 4983230072969 + 3 ^ 40 * 5237863 * 2
def baseEnd_5237863 : Nat := 2689541321400945570624013

theorem tailTrace_5237863 : CollatzResearch.WordTrace tailWord_5237863 prefixEnd_5237863 2689541321400945570624013 := by
  unfold tailWord_5237863
  simp only [CollatzResearch.WordTrace]
  refine ⟨191040558223124381626286243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127360372148749587750857495 191040558223124381626286243)
  ·
    refine ⟨286560837334686572439429365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191040558223124381626286243 286560837334686572439429365)
    ·
      refine ⟨26865078500126866166196503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 286560837334686572439429365 26865078500126866166196503)
      ·
        refine ⟨40297617750190299249294755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26865078500126866166196503 40297617750190299249294755)
        ·
          refine ⟨60446426625285448873942133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40297617750190299249294755 60446426625285448873942133)
          ·
            refine ⟨5666852496120510831932075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60446426625285448873942133 5666852496120510831932075)
            ·
              refine ⟨8500278744180766247898113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5666852496120510831932075 8500278744180766247898113)
              ·
                refine ⟨6375209058135574685923585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8500278744180766247898113 6375209058135574685923585)
                ·
                  refine ⟨4781406793601681014442689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6375209058135574685923585 4781406793601681014442689)
                  ·
                    refine ⟨3586055095201260760832017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4781406793601681014442689 3586055095201260760832017)
                    ·
                      refine ⟨2689541321400945570624013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3586055095201260760832017 2689541321400945570624013)
                      ·
                        rfl

theorem cell23_5237863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_5237863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237863 prefixEnd_5237863 := by exact prefixLift 5237863
  have htrace : WordTrace (prefixWord ++ tailWord_5237863) baseStart_5237863 baseEnd_5237863 := by
    simpa [prefixWord, tailWord_5237863, baseEnd_5237863] using wordTrace_append hprefix tailTrace_5237863
  have hstable : (prefixWord ++ tailWord_5237863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237863).length < 2 ^ (prefixWord ++ tailWord_5237863).sum := by decide
  have hdescent : baseEnd_5237863 < baseStart_5237863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237869 : List Nat := [1, 5, 1, 1, 2, 2, 2, 4, 5]
def baseStart_5237869 : Nat := 118140960795 + 5237869 * 2 ^ 59
def prefixEnd_5237869 : Nat := 4983230072969 + 3 ^ 40 * 5237869 * 2
def baseEnd_5237869 : Nat := 298838266920541394127665

theorem tailTrace_5237869 : CollatzResearch.WordTrace tailWord_5237869 prefixEnd_5237869 298838266920541394127665 := by
  unfold tailWord_5237869
  simp only [CollatzResearch.WordTrace]
  refine ⟨191040777061102644651004661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127360518040735096434003107 191040777061102644651004661)
  ·
    refine ⟨17910072849478372936031687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 191040777061102644651004661 17910072849478372936031687)
    ·
      refine ⟨26865109274217559404047531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17910072849478372936031687 26865109274217559404047531)
      ·
        refine ⟨40297663911326339106071297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26865109274217559404047531 40297663911326339106071297)
        ·
          refine ⟨30223247933494754329553473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40297663911326339106071297 30223247933494754329553473)
          ·
            refine ⟨22667435950121065747165105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30223247933494754329553473 22667435950121065747165105)
            ·
              refine ⟨17000576962590799310373829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22667435950121065747165105 17000576962590799310373829)
              ·
                refine ⟨3187608180485774870695093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17000576962590799310373829 3187608180485774870695093)
                ·
                  refine ⟨298838266920541394127665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3187608180485774870695093 298838266920541394127665)
                  ·
                    rfl

theorem cell23_5237869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_5237869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237869 prefixEnd_5237869 := by exact prefixLift 5237869
  have htrace : WordTrace (prefixWord ++ tailWord_5237869) baseStart_5237869 baseEnd_5237869 := by
    simpa [prefixWord, tailWord_5237869, baseEnd_5237869] using wordTrace_append hprefix tailTrace_5237869
  have hstable : (prefixWord ++ tailWord_5237869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237869).length < 2 ^ (prefixWord ++ tailWord_5237869).sum := by decide
  have hdescent : baseEnd_5237869 < baseStart_5237869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5237895 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 1, 10]
def baseStart_5237895 : Nat := 118140960795 + 5237895 * 2 ^ 59
def prefixEnd_5237895 : Nat := 4983230072969 + 3 ^ 40 * 5237895 * 2
def baseEnd_5237895 : Nat := 896519250927296481807955

theorem tailTrace_5237895 : CollatzResearch.WordTrace tailWord_5237895 prefixEnd_5237895 896519250927296481807955 := by
  unfold tailWord_5237895
  simp only [CollatzResearch.WordTrace]
  refine ⟨191041725359008451091451139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127361150239338967394300759 191041725359008451091451139)
  ·
    refine ⟨286562588038512676637176709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191041725359008451091451139 286562588038512676637176709)
    ·
      refine ⟨53730485257221126869470633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286562588038512676637176709 53730485257221126869470633)
      ·
        refine ⟨40297863942915845152102975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53730485257221126869470633 40297863942915845152102975)
        ·
          refine ⟨60446795914373767728154463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40297863942915845152102975 60446795914373767728154463)
          ·
            refine ⟨90670193871560651592231695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60446795914373767728154463 90670193871560651592231695)
            ·
              refine ⟨136005290807340977388347543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90670193871560651592231695 136005290807340977388347543)
              ·
                refine ⟨204007936211011466082521315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136005290807340977388347543 204007936211011466082521315)
                ·
                  refine ⟨306011904316517199123781973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204007936211011466082521315 306011904316517199123781973)
                  ·
                    refine ⟨896519250927296481807955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 306011904316517199123781973 896519250927296481807955)
                    ·
                      rfl

theorem cell23_5237895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_5237895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5237895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5237895 prefixEnd_5237895 := by exact prefixLift 5237895
  have htrace : WordTrace (prefixWord ++ tailWord_5237895) baseStart_5237895 baseEnd_5237895 := by
    simpa [prefixWord, tailWord_5237895, baseEnd_5237895] using wordTrace_append hprefix tailTrace_5237895
  have hstable : (prefixWord ++ tailWord_5237895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5237895).length < 2 ^ (prefixWord ++ tailWord_5237895).sum := by decide
  have hdescent : baseEnd_5237895 < baseStart_5237895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5237895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
