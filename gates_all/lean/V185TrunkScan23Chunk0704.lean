import V185TrunkScan23Chunk0703

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4162473 : List Nat := [1, 2, 1, 1, 1, 1, 6, 5, 5]
def baseStart_4162473 : Nat := 118140960795 + 4162473 * 2 ^ 59
def prefixEnd_4162473 : Nat := 4983230072969 + 3 ^ 40 * 4162473 * 2
def baseEnd_4162473 : Nat := 237483262262488670993849

theorem tailTrace_4162473 : CollatzResearch.WordTrace tailWord_4162473 prefixEnd_4162473 237483262262488670993849 := by
  unfold tailWord_4162473
  simp only [CollatzResearch.WordTrace]
  refine ⟨151817862649078689636364073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101211908432719126424242715 151817862649078689636364073)
  ·
    refine ⟨113863396986809017227273055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151817862649078689636364073 113863396986809017227273055)
    ·
      refine ⟨170795095480213525840909583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113863396986809017227273055 170795095480213525840909583)
      ·
        refine ⟨256192643220320288761364375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170795095480213525840909583 256192643220320288761364375)
        ·
          refine ⟨384288964830480433142046563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256192643220320288761364375 384288964830480433142046563)
          ·
            refine ⟨576433447245720649713069845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384288964830480433142046563 576433447245720649713069845)
            ·
              refine ⟨27020317839643155455300149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 576433447245720649713069845 27020317839643155455300149)
              ·
                refine ⟨2533154797466545823934389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27020317839643155455300149 2533154797466545823934389)
                ·
                  refine ⟨237483262262488670993849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2533154797466545823934389 237483262262488670993849)
                  ·
                    rfl

theorem cell23_4162473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 5].length) (baseStart_4162473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162473 prefixEnd_4162473 := by exact prefixLift 4162473
  have htrace : WordTrace (prefixWord ++ tailWord_4162473) baseStart_4162473 baseEnd_4162473 := by
    simpa [prefixWord, tailWord_4162473, baseEnd_4162473] using wordTrace_append hprefix tailTrace_4162473
  have hstable : (prefixWord ++ tailWord_4162473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162473).length < 2 ^ (prefixWord ++ tailWord_4162473).sum := by decide
  have hdescent : baseEnd_4162473 < baseStart_4162473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162520 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 2, 5]
def baseStart_4162520 : Nat := 118140960795 + 4162520 * 2 ^ 59
def prefixEnd_4162520 : Nat := 4983230072969 + 3 ^ 40 * 4162520 * 2
def baseEnd_4162520 : Nat := 712457831317719785018975

theorem tailTrace_4162520 : CollatzResearch.WordTrace tailWord_4162520 prefixEnd_4162520 712457831317719785018975 := by
  unfold tailWord_4162520
  simp only [CollatzResearch.WordTrace]
  refine ⟨75909788439954208331662507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101213051253272277775550009 75909788439954208331662507)
  ·
    refine ⟨113864682659931312497493761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75909788439954208331662507 113864682659931312497493761)
    ·
      refine ⟨85398511994948484373120321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113864682659931312497493761 85398511994948484373120321)
      ·
        refine ⟨64048883996211363279840241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85398511994948484373120321 64048883996211363279840241)
        ·
          refine ⟨48036662997158522459880181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64048883996211363279840241 48036662997158522459880181)
          ·
            refine ⟨4503437155983611480613767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48036662997158522459880181 4503437155983611480613767)
            ·
              refine ⟨6755155733975417220920651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503437155983611480613767 6755155733975417220920651)
              ·
                refine ⟨10132733600963125831380977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755155733975417220920651 10132733600963125831380977)
                ·
                  refine ⟨7599550200722344373535733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10132733600963125831380977 7599550200722344373535733)
                  ·
                    refine ⟨712457831317719785018975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7599550200722344373535733 712457831317719785018975)
                    ·
                      rfl

theorem cell23_4162520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_4162520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162520 prefixEnd_4162520 := by exact prefixLift 4162520
  have htrace : WordTrace (prefixWord ++ tailWord_4162520) baseStart_4162520 baseEnd_4162520 := by
    simpa [prefixWord, tailWord_4162520, baseEnd_4162520] using wordTrace_append hprefix tailTrace_4162520
  have hstable : (prefixWord ++ tailWord_4162520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162520).length < 2 ^ (prefixWord ++ tailWord_4162520).sum := by decide
  have hdescent : baseEnd_4162520 < baseStart_4162520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162584 : List Nat := [2, 1, 2, 3, 2, 4, 1, 3, 1, 4]
def baseStart_4162584 : Nat := 118140960795 + 4162584 * 2 ^ 59
def prefixEnd_4162584 : Nat := 4983230072969 + 3 ^ 40 * 4162584 * 2
def baseEnd_4162584 : Nat := 712468785571682368218877

theorem tailTrace_4162584 : CollatzResearch.WordTrace tailWord_4162584 prefixEnd_4162584 712468785571682368218877 := by
  unfold tailWord_4162584
  simp only [CollatzResearch.WordTrace]
  refine ⟨75910955575838277796827403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101214607434451037062436537 75910955575838277796827403)
  ·
    refine ⟨113866433363757416695241105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75910955575838277796827403 113866433363757416695241105)
    ·
      refine ⟨85399825022818062521430829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113866433363757416695241105 85399825022818062521430829)
      ·
        refine ⟨32024934383556773445536561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85399825022818062521430829 32024934383556773445536561)
        ·
          refine ⟨24018700787667580084152421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32024934383556773445536561 24018700787667580084152421)
          ·
            refine ⟨4503506397687671265778579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24018700787667580084152421 4503506397687671265778579)
            ·
              refine ⟨6755259596531506898667869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503506397687671265778579 6755259596531506898667869)
              ·
                refine ⟨2533222348699315087000451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6755259596531506898667869 2533222348699315087000451)
                ·
                  refine ⟨3799833523048972630500677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533222348699315087000451 3799833523048972630500677)
                  ·
                    refine ⟨712468785571682368218877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3799833523048972630500677 712468785571682368218877)
                    ·
                      rfl

theorem cell23_4162584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_4162584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162584 prefixEnd_4162584 := by exact prefixLift 4162584
  have htrace : WordTrace (prefixWord ++ tailWord_4162584) baseStart_4162584 baseEnd_4162584 := by
    simpa [prefixWord, tailWord_4162584, baseEnd_4162584] using wordTrace_append hprefix tailTrace_4162584
  have hstable : (prefixWord ++ tailWord_4162584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162584).length < 2 ^ (prefixWord ++ tailWord_4162584).sum := by decide
  have hdescent : baseEnd_4162584 < baseStart_4162584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162613 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_4162613 : Nat := 118140960795 + 4162613 * 2 ^ 59
def prefixEnd_4162613 : Nat := 4983230072969 + 3 ^ 40 * 4162613 * 2
def baseEnd_4162613 : Nat := 2137421247654027491193997

theorem tailTrace_4162613 : CollatzResearch.WordTrace tailWord_4162613 prefixEnd_4162613 2137421247654027491193997 := by
  unfold tailWord_4162613
  simp only [CollatzResearch.WordTrace]
  refine ⟨151822968868571493546460493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101215312579047662364306995 151822968868571493546460493)
  ·
    refine ⟨56933613325714310079922685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151822968868571493546460493 56933613325714310079922685)
    ·
      refine ⟨21350104997142866279971007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56933613325714310079922685 21350104997142866279971007)
      ·
        refine ⟨32025157495714299419956511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21350104997142866279971007 32025157495714299419956511)
        ·
          refine ⟨48037736243571449129934767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32025157495714299419956511 48037736243571449129934767)
          ·
            refine ⟨72056604365357173694902151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48037736243571449129934767 72056604365357173694902151)
            ·
              refine ⟨108084906548035760542353227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72056604365357173694902151 108084906548035760542353227)
              ·
                refine ⟨162127359822053640813529841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108084906548035760542353227 162127359822053640813529841)
                ·
                  refine ⟨121595519866540230610147381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162127359822053640813529841 121595519866540230610147381)
                  ·
                    refine ⟨11399579987488146619701317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121595519866540230610147381 11399579987488146619701317)
                    ·
                      refine ⟨2137421247654027491193997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11399579987488146619701317 2137421247654027491193997)
                      ·
                        rfl

theorem cell23_4162613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_4162613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162613 prefixEnd_4162613 := by exact prefixLift 4162613
  have htrace : WordTrace (prefixWord ++ tailWord_4162613) baseStart_4162613 baseEnd_4162613 := by
    simpa [prefixWord, tailWord_4162613, baseEnd_4162613] using wordTrace_append hprefix tailTrace_4162613
  have hstable : (prefixWord ++ tailWord_4162613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162613).length < 2 ^ (prefixWord ++ tailWord_4162613).sum := by decide
  have hdescent : baseEnd_4162613 < baseStart_4162613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162614 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_4162614 : Nat := 118140960795 + 4162614 * 2 ^ 59
def prefixEnd_4162614 : Nat := 4983230072969 + 3 ^ 40 * 4162614 * 2
def baseEnd_4162614 : Nat := 237491306792742443031277

theorem tailTrace_4162614 : CollatzResearch.WordTrace tailWord_4162614 prefixEnd_4162614 237491306792742443031277 := by
  unfold tailWord_4162614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488937833847991919827931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101215336894378580478164597 9488937833847991919827931)
  ·
    refine ⟨14233406750771987879741897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9488937833847991919827931 14233406750771987879741897)
    ·
      refine ⟨10675055063078990909806423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14233406750771987879741897 10675055063078990909806423)
      ·
        refine ⟨16012582594618486364709635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10675055063078990909806423 16012582594618486364709635)
        ·
          refine ⟨24018873891927729547064453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16012582594618486364709635 24018873891927729547064453)
          ·
            refine ⟨4503538854736449290074585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24018873891927729547064453 4503538854736449290074585)
            ·
              refine ⟨3377654141052336967555939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4503538854736449290074585 3377654141052336967555939)
              ·
                refine ⟨5066481211578505451333909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3377654141052336967555939 5066481211578505451333909)
                ·
                  refine ⟨237491306792742443031277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5066481211578505451333909 237491306792742443031277)
                  ·
                    rfl

theorem cell23_4162614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_4162614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162614 prefixEnd_4162614 := by exact prefixLift 4162614
  have htrace : WordTrace (prefixWord ++ tailWord_4162614) baseStart_4162614 baseEnd_4162614 := by
    simpa [prefixWord, tailWord_4162614, baseEnd_4162614] using wordTrace_append hprefix tailTrace_4162614
  have hstable : (prefixWord ++ tailWord_4162614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162614).length < 2 ^ (prefixWord ++ tailWord_4162614).sum := by decide
  have hdescent : baseEnd_4162614 < baseStart_4162614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162623 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 1, 6]
def baseStart_4162623 : Nat := 118140960795 + 4162623 * 2 ^ 59
def prefixEnd_4162623 : Nat := 4983230072969 + 3 ^ 40 * 4162623 * 2
def baseEnd_4162623 : Nat := 712475460820190817356317

theorem tailTrace_4162623 : CollatzResearch.WordTrace tailWord_4162623 prefixEnd_4162623 712475460820190817356317 := by
  unfold tailWord_4162623
  simp only [CollatzResearch.WordTrace]
  refine ⟨151823333598535265254324523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101215555732356843502883015 151823333598535265254324523)
  ·
    refine ⟨227735000397802897881486785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151823333598535265254324523 227735000397802897881486785)
    ·
      refine ⟨170801250298352173411115089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227735000397802897881486785 170801250298352173411115089)
      ·
        refine ⟨128100937723764130058336317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170801250298352173411115089 128100937723764130058336317)
        ·
          refine ⟨48037851646411548771876119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128100937723764130058336317 48037851646411548771876119)
          ·
            refine ⟨72056777469617323157814179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48037851646411548771876119 72056777469617323157814179)
            ·
              refine ⟨108085166204425984736721269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72056777469617323157814179 108085166204425984736721269)
              ·
                refine ⟨10132984331664936069067619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108085166204425984736721269 10132984331664936069067619)
                ·
                  refine ⟨15199476497497404103601429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10132984331664936069067619 15199476497497404103601429)
                  ·
                    refine ⟨712475460820190817356317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15199476497497404103601429 712475460820190817356317)
                    ·
                      rfl

theorem cell23_4162623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_4162623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162623 prefixEnd_4162623 := by exact prefixLift 4162623
  have htrace : WordTrace (prefixWord ++ tailWord_4162623) baseStart_4162623 baseEnd_4162623 := by
    simpa [prefixWord, tailWord_4162623, baseEnd_4162623] using wordTrace_append hprefix tailTrace_4162623
  have hstable : (prefixWord ++ tailWord_4162623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162623).length < 2 ^ (prefixWord ++ tailWord_4162623).sum := by decide
  have hdescent : baseEnd_4162623 < baseStart_4162623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162643 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 4]
def baseStart_4162643 : Nat := 118140960795 + 4162643 * 2 ^ 59
def prefixEnd_4162643 : Nat := 4983230072969 + 3 ^ 40 * 4162643 * 2
def baseEnd_4162643 : Nat := 2137436652073662373818859

theorem tailTrace_4162643 : CollatzResearch.WordTrace tailWord_4162643 prefixEnd_4162643 2137436652073662373818859 := by
  unfold tailWord_4162643
  simp only [CollatzResearch.WordTrace]
  refine ⟨151824063058462808670052583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101216042038975205780035055 151824063058462808670052583)
  ·
    refine ⟨227736094587694213005078875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151824063058462808670052583 227736094587694213005078875)
    ·
      refine ⟨341604141881541319507618313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227736094587694213005078875 341604141881541319507618313)
      ·
        refine ⟨256203106411155989630713735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341604141881541319507618313 256203106411155989630713735)
        ·
          refine ⟨384304659616733984446070603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256203106411155989630713735 384304659616733984446070603)
          ·
            refine ⟨576456989425100976669105905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384304659616733984446070603 576456989425100976669105905)
            ·
              refine ⟨432342742068825732501829429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576456989425100976669105905 432342742068825732501829429)
              ·
                refine ⟨40532132068952412422046509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432342742068825732501829429 40532132068952412422046509)
                ·
                  refine ⟨15199549525857154658267441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40532132068952412422046509 15199549525857154658267441)
                  ·
                    refine ⟨11399662144392865993700581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15199549525857154658267441 11399662144392865993700581)
                    ·
                      refine ⟨2137436652073662373818859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11399662144392865993700581 2137436652073662373818859)
                      ·
                        rfl

theorem cell23_4162643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_4162643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162643 prefixEnd_4162643 := by exact prefixLift 4162643
  have htrace : WordTrace (prefixWord ++ tailWord_4162643) baseStart_4162643 baseEnd_4162643 := by
    simpa [prefixWord, tailWord_4162643, baseEnd_4162643] using wordTrace_append hprefix tailTrace_4162643
  have hstable : (prefixWord ++ tailWord_4162643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162643).length < 2 ^ (prefixWord ++ tailWord_4162643).sum := by decide
  have hdescent : baseEnd_4162643 < baseStart_4162643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162658 : List Nat := [3, 3, 2, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4162658 : Nat := 118140960795 + 4162658 * 2 ^ 59
def prefixEnd_4162658 : Nat := 4983230072969 + 3 ^ 40 * 4162658 * 2
def baseEnd_4162658 : Nat := 2137444354283479815131291

theorem tailTrace_4162658 : CollatzResearch.WordTrace tailWord_4162658 prefixEnd_4162658 2137444354283479815131291 := by
  unfold tailWord_4162658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37956152538352116557962157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101216406768938977487899085 37956152538352116557962157)
  ·
    refine ⟨14233557201882043709235809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37956152538352116557962157 14233557201882043709235809)
    ·
      refine ⟨10675167901411532781926857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14233557201882043709235809 10675167901411532781926857)
      ·
        refine ⟨8006375926058649586445143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10675167901411532781926857 8006375926058649586445143)
        ·
          refine ⟨12009563889087974379667715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006375926058649586445143 12009563889087974379667715)
          ·
            refine ⟨18014345833631961569501573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12009563889087974379667715 18014345833631961569501573)
            ·
              refine ⟨3377689843805992794281545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18014345833631961569501573 3377689843805992794281545)
              ·
                refine ⟨2533267382854494595711159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3377689843805992794281545 2533267382854494595711159)
                ·
                  refine ⟨3799901074281741893566739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533267382854494595711159 3799901074281741893566739)
                  ·
                    refine ⟨5699851611422612840350109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3799901074281741893566739 5699851611422612840350109)
                    ·
                      refine ⟨2137444354283479815131291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5699851611422612840350109 2137444354283479815131291)
                      ·
                        rfl

theorem cell23_4162658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4162658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162658 prefixEnd_4162658 := by exact prefixLift 4162658
  have htrace : WordTrace (prefixWord ++ tailWord_4162658) baseStart_4162658 baseEnd_4162658 := by
    simpa [prefixWord, tailWord_4162658, baseEnd_4162658] using wordTrace_append hprefix tailTrace_4162658
  have hstable : (prefixWord ++ tailWord_4162658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162658).length < 2 ^ (prefixWord ++ tailWord_4162658).sum := by decide
  have hdescent : baseEnd_4162658 < baseStart_4162658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162670 : List Nat := [4, 1, 2, 2, 1, 2, 3, 8]
def baseStart_4162670 : Nat := 118140960795 + 4162670 * 2 ^ 59
def prefixEnd_4162670 : Nat := 4983230072969 + 3 ^ 40 * 4162670 * 2
def baseEnd_4162670 : Nat := 79164833927827176599305

theorem tailTrace_4162670 : CollatzResearch.WordTrace tailWord_4162670 prefixEnd_4162670 79164833927827176599305 := by
  unfold tailWord_4162670
  simp only [CollatzResearch.WordTrace]
  refine ⟨18978130978670624035160683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101216698552909994854190309 18978130978670624035160683)
  ·
    refine ⟨28467196468005936052741025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18978130978670624035160683 28467196468005936052741025)
    ·
      refine ⟨21350397351004452039555769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28467196468005936052741025 21350397351004452039555769)
      ·
        refine ⟨16012798013253339029666827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21350397351004452039555769 16012798013253339029666827)
        ·
          refine ⟨24019197019880008544500241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16012798013253339029666827 24019197019880008544500241)
          ·
            refine ⟨18014397764910006408375181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24019197019880008544500241 18014397764910006408375181)
            ·
              refine ⟨6755399161841252403140693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18014397764910006408375181 6755399161841252403140693)
              ·
                refine ⟨79164833927827176599305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6755399161841252403140693 79164833927827176599305)
                ·
                  rfl

theorem cell23_4162670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_4162670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162670 prefixEnd_4162670 := by exact prefixLift 4162670
  have htrace : WordTrace (prefixWord ++ tailWord_4162670) baseStart_4162670 baseEnd_4162670 := by
    simpa [prefixWord, tailWord_4162670, baseEnd_4162670] using wordTrace_append hprefix tailTrace_4162670
  have hstable : (prefixWord ++ tailWord_4162670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162670).length < 2 ^ (prefixWord ++ tailWord_4162670).sum := by decide
  have hdescent : baseEnd_4162670 < baseStart_4162670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162680 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_4162680 : Nat := 118140960795 + 4162680 * 2 ^ 59
def prefixEnd_4162680 : Nat := 4983230072969 + 3 ^ 40 * 4162680 * 2
def baseEnd_4162680 : Nat := 2137455650857878729056189

theorem tailTrace_4162680 : CollatzResearch.WordTrace tailWord_4162680 prefixEnd_4162680 2137455650857878729056189 := by
  unfold tailWord_4162680
  simp only [CollatzResearch.WordTrace]
  refine ⟨75912706279664381994574747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101216941706219175992766329 75912706279664381994574747)
  ·
    refine ⟨113869059419496572991862121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75912706279664381994574747 113869059419496572991862121)
    ·
      refine ⟨85401794564622429743896591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113869059419496572991862121 85401794564622429743896591)
      ·
        refine ⟨128102691846933644615844887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85401794564622429743896591 128102691846933644615844887)
        ·
          refine ⟨192154037770400466923767331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128102691846933644615844887 192154037770400466923767331)
          ·
            refine ⟨288231056655600700385650997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192154037770400466923767331 288231056655600700385650997)
            ·
              refine ⟨27021661561462565661154781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288231056655600700385650997 27021661561462565661154781)
              ·
                refine ⟨10133123085548462122933043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27021661561462565661154781 10133123085548462122933043)
                ·
                  refine ⟨15199684628322693184399565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10133123085548462122933043 15199684628322693184399565)
                  ·
                    refine ⟨5699881735621009944149837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15199684628322693184399565 5699881735621009944149837)
                    ·
                      refine ⟨2137455650857878729056189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5699881735621009944149837 2137455650857878729056189)
                      ·
                        rfl

theorem cell23_4162680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_4162680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162680 prefixEnd_4162680 := by exact prefixLift 4162680
  have htrace : WordTrace (prefixWord ++ tailWord_4162680) baseStart_4162680 baseEnd_4162680 := by
    simpa [prefixWord, tailWord_4162680, baseEnd_4162680] using wordTrace_append hprefix tailTrace_4162680
  have hstable : (prefixWord ++ tailWord_4162680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162680).length < 2 ^ (prefixWord ++ tailWord_4162680).sum := by decide
  have hdescent : baseEnd_4162680 < baseStart_4162680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162714 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3]
def baseStart_4162714 : Nat := 118140960795 + 4162714 * 2 ^ 59
def prefixEnd_4162714 : Nat := 4983230072969 + 3 ^ 40 * 4162714 * 2
def baseEnd_4162714 : Nat := 2137473109200131596031033

theorem tailTrace_4162714 : CollatzResearch.WordTrace tailWord_4162714 prefixEnd_4162714 2137473109200131596031033 := by
  unfold tailWord_4162714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37956663160301396948971799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101217768427470391863924797 37956663160301396948971799)
  ·
    refine ⟨56934994740452095423457699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37956663160301396948971799 56934994740452095423457699)
    ·
      refine ⟨85402492110678143135186549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56934994740452095423457699 85402492110678143135186549)
      ·
        refine ⟨8006483635376075918923739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85402492110678143135186549 8006483635376075918923739)
        ·
          refine ⟨12009725453064113878385609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006483635376075918923739 12009725453064113878385609)
          ·
            refine ⟨9007294089798085408789207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12009725453064113878385609 9007294089798085408789207)
            ·
              refine ⟨13510941134697128113183811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007294089798085408789207 13510941134697128113183811)
              ·
                refine ⟨20266411702045692169775717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13510941134697128113183811 20266411702045692169775717)
                ·
                  refine ⟨3799952194133567281832947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20266411702045692169775717 3799952194133567281832947)
                  ·
                    refine ⟨5699928291200350922749421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3799952194133567281832947 5699928291200350922749421)
                    ·
                      refine ⟨2137473109200131596031033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5699928291200350922749421 2137473109200131596031033)
                      ·
                        rfl

theorem cell23_4162714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_4162714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162714 prefixEnd_4162714 := by exact prefixLift 4162714
  have htrace : WordTrace (prefixWord ++ tailWord_4162714) baseStart_4162714 baseEnd_4162714 := by
    simpa [prefixWord, tailWord_4162714, baseEnd_4162714] using wordTrace_append hprefix tailTrace_4162714
  have hstable : (prefixWord ++ tailWord_4162714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162714).length < 2 ^ (prefixWord ++ tailWord_4162714).sum := by decide
  have hdescent : baseEnd_4162714 < baseStart_4162714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162770 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4162770 : Nat := 118140960795 + 4162770 * 2 ^ 59
def prefixEnd_4162770 : Nat := 4983230072969 + 3 ^ 40 * 4162770 * 2
def baseEnd_4162770 : Nat := 2137501864116783376930775

theorem tailTrace_4162770 : CollatzResearch.WordTrace tailWord_4162770 prefixEnd_4162770 2137501864116783376930775 := by
  unfold tailWord_4162770
  simp only [CollatzResearch.WordTrace]
  refine ⟨37957173782250677339981441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101219130086001806239950509 37957173782250677339981441)
  ·
    refine ⟨28467880336688008004986081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37957173782250677339981441 28467880336688008004986081)
    ·
      refine ⟨21350910252516006003739561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28467880336688008004986081 21350910252516006003739561)
      ·
        refine ⟨16013182689387004502804671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21350910252516006003739561 16013182689387004502804671)
        ·
          refine ⟨24019774034080506754207007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16013182689387004502804671 24019774034080506754207007)
          ·
            refine ⟨36029661051120760131310511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24019774034080506754207007 36029661051120760131310511)
            ·
              refine ⟨54044491576681140196965767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36029661051120760131310511 54044491576681140196965767)
              ·
                refine ⟨81066737365021710295448651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54044491576681140196965767 81066737365021710295448651)
                ·
                  refine ⟨121600106047532565443172977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81066737365021710295448651 121600106047532565443172977)
                  ·
                    refine ⟨91200079535649424082379733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121600106047532565443172977 91200079535649424082379733)
                    ·
                      refine ⟨2137501864116783376930775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91200079535649424082379733 2137501864116783376930775)
                      ·
                        rfl

theorem cell23_4162770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4162770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162770 prefixEnd_4162770 := by exact prefixLift 4162770
  have htrace : WordTrace (prefixWord ++ tailWord_4162770) baseStart_4162770 baseEnd_4162770 := by
    simpa [prefixWord, tailWord_4162770, baseEnd_4162770] using wordTrace_append hprefix tailTrace_4162770
  have hstable : (prefixWord ++ tailWord_4162770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162770).length < 2 ^ (prefixWord ++ tailWord_4162770).sum := by decide
  have hdescent : baseEnd_4162770 < baseStart_4162770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162827 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 4]
def baseStart_4162827 : Nat := 118140960795 + 4162827 * 2 ^ 59
def prefixEnd_4162827 : Nat := 4983230072969 + 3 ^ 40 * 4162827 * 2
def baseEnd_4162827 : Nat := 2137531132514089653918013

theorem tailTrace_4162827 : CollatzResearch.WordTrace tailWord_4162827 prefixEnd_4162827 2137531132514089653918013 := by
  unfold tailWord_4162827
  simp only [CollatzResearch.WordTrace]
  refine ⟨151830774089796208094750735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101220516059864138729833823 151830774089796208094750735)
  ·
    refine ⟨227746161134694312142126103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151830774089796208094750735 227746161134694312142126103)
    ·
      refine ⟨341619241702041468213189155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227746161134694312142126103 341619241702041468213189155)
      ·
        refine ⟨512428862553062202319783733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341619241702041468213189155 512428862553062202319783733)
        ·
          refine ⟨48040205864349581467479725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 512428862553062202319783733 48040205864349581467479725)
          ·
            refine ⟨18015077199131093050304897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48040205864349581467479725 18015077199131093050304897)
            ·
              refine ⟨13511307899348319787728673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18015077199131093050304897 13511307899348319787728673)
              ·
                refine ⟨10133480924511239840796505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13511307899348319787728673 10133480924511239840796505)
                ·
                  refine ⟨7600110693383429880597379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10133480924511239840796505 7600110693383429880597379)
                  ·
                    refine ⟨11400166040075144820896069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600110693383429880597379 11400166040075144820896069)
                    ·
                      refine ⟨2137531132514089653918013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11400166040075144820896069 2137531132514089653918013)
                      ·
                        rfl

theorem cell23_4162827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 4].length) (baseStart_4162827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162827 prefixEnd_4162827 := by exact prefixLift 4162827
  have htrace : WordTrace (prefixWord ++ tailWord_4162827) baseStart_4162827 baseEnd_4162827 := by
    simpa [prefixWord, tailWord_4162827, baseEnd_4162827] using wordTrace_append hprefix tailTrace_4162827
  have hstable : (prefixWord ++ tailWord_4162827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162827).length < 2 ^ (prefixWord ++ tailWord_4162827).sum := by decide
  have hdescent : baseEnd_4162827 < baseStart_4162827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162837 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_4162837 : Nat := 118140960795 + 4162837 * 2 ^ 59
def prefixEnd_4162837 : Nat := 4983230072969 + 3 ^ 40 * 4162837 * 2
def baseEnd_4162837 : Nat := 712512089106878204930989

theorem tailTrace_4162837 : CollatzResearch.WordTrace tailWord_4162837 prefixEnd_4162837 712512089106878204930989 := by
  unfold tailWord_4162837
  simp only [CollatzResearch.WordTrace]
  refine ⟨151831138819759979802614765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101220759213173319868409843 151831138819759979802614765)
  ·
    refine ⟨56936677057409992425980537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151831138819759979802614765 56936677057409992425980537)
    ·
      refine ⟨42702507793057494319485403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56936677057409992425980537 42702507793057494319485403)
      ·
        refine ⟨64053761689586241479228105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42702507793057494319485403 64053761689586241479228105)
        ·
          refine ⟨48040321267189681109421079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64053761689586241479228105 48040321267189681109421079)
          ·
            refine ⟨72060481900784521664131619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48040321267189681109421079 72060481900784521664131619)
            ·
              refine ⟨108090722851176782496197429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72060481900784521664131619 108090722851176782496197429)
              ·
                refine ⟨10133505267297823359018509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108090722851176782496197429 10133505267297823359018509)
                ·
                  refine ⟨3800064475236683759631941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10133505267297823359018509 3800064475236683759631941)
                  ·
                    refine ⟨712512089106878204930989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800064475236683759631941 712512089106878204930989)
                    ·
                      rfl

theorem cell23_4162837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_4162837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162837 prefixEnd_4162837 := by exact prefixLift 4162837
  have htrace : WordTrace (prefixWord ++ tailWord_4162837) baseStart_4162837 baseEnd_4162837 := by
    simpa [prefixWord, tailWord_4162837, baseEnd_4162837] using wordTrace_append hprefix tailTrace_4162837
  have hstable : (prefixWord ++ tailWord_4162837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162837).length < 2 ^ (prefixWord ++ tailWord_4162837).sum := by decide
  have hdescent : baseEnd_4162837 < baseStart_4162837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162861 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_4162861 : Nat := 118140960795 + 4162861 * 2 ^ 59
def prefixEnd_4162861 : Nat := 4983230072969 + 3 ^ 40 * 4162861 * 2
def baseEnd_4162861 : Nat := 2137548590856342520892857

theorem tailTrace_4162861 : CollatzResearch.WordTrace tailWord_4162861 prefixEnd_4162861 2137548590856342520892857 := by
  unfold tailWord_4162861
  simp only [CollatzResearch.WordTrace]
  refine ⟨151832014171673031901488437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101221342781115354600992291 151832014171673031901488437)
  ·
    refine ⟨14234251328594346740764541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151832014171673031901488437 14234251328594346740764541)
    ·
      refine ⟨5337844248222880027786703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14234251328594346740764541 5337844248222880027786703)
      ·
        refine ⟨8006766372334320041680055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337844248222880027786703 8006766372334320041680055)
        ·
          refine ⟨12010149558501480062520083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006766372334320041680055 12010149558501480062520083)
          ·
            refine ⟨18015224337752220093780125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12010149558501480062520083 18015224337752220093780125)
            ·
              refine ⟨6755709126657082535167547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18015224337752220093780125 6755709126657082535167547)
              ·
                refine ⟨10133563689985623802751321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755709126657082535167547 10133563689985623802751321)
                ·
                  refine ⟨7600172767489217852063491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10133563689985623802751321 7600172767489217852063491)
                  ·
                    refine ⟨11400259151233826778095237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600172767489217852063491 11400259151233826778095237)
                    ·
                      refine ⟨2137548590856342520892857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11400259151233826778095237 2137548590856342520892857)
                      ·
                        rfl

theorem cell23_4162861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_4162861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162861 prefixEnd_4162861 := by exact prefixLift 4162861
  have htrace : WordTrace (prefixWord ++ tailWord_4162861) baseStart_4162861 baseEnd_4162861 := by
    simpa [prefixWord, tailWord_4162861, baseEnd_4162861] using wordTrace_append hprefix tailTrace_4162861
  have hstable : (prefixWord ++ tailWord_4162861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162861).length < 2 ^ (prefixWord ++ tailWord_4162861).sum := by decide
  have hdescent : baseEnd_4162861 < baseStart_4162861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162884 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 8]
def baseStart_4162884 : Nat := 118140960795 + 4162884 * 2 ^ 59
def prefixEnd_4162884 : Nat := 4983230072969 + 3 ^ 40 * 4162884 * 2
def baseEnd_4162884 : Nat := 237506711212377325656139

theorem tailTrace_4162884 : CollatzResearch.WordTrace tailWord_4162884 prefixEnd_4162884 237506711212377325656139 := by
  unfold tailWord_4162884
  simp only [CollatzResearch.WordTrace]
  refine ⟨75916426525294853414787853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101221902033726471219717137 75916426525294853414787853)
  ·
    refine ⟨28468659946985570030545445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75916426525294853414787853 28468659946985570030545445)
    ·
      refine ⟨5337873740059794380727271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28468659946985570030545445 5337873740059794380727271)
      ·
        refine ⟨8006810610089691571090907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337873740059794380727271 8006810610089691571090907)
        ·
          refine ⟨12010215915134537356636361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006810610089691571090907 12010215915134537356636361)
          ·
            refine ⟨9007661936350903017477271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12010215915134537356636361 9007661936350903017477271)
            ·
              refine ⟨13511492904526354526215907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9007661936350903017477271 13511492904526354526215907)
              ·
                refine ⟨20267239356789531789323861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13511492904526354526215907 20267239356789531789323861)
                ·
                  refine ⟨237506711212377325656139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20267239356789531789323861 237506711212377325656139)
                  ·
                    rfl

theorem cell23_4162884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_4162884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162884 prefixEnd_4162884 := by exact prefixLift 4162884
  have htrace : WordTrace (prefixWord ++ tailWord_4162884) baseStart_4162884 baseEnd_4162884 := by
    simpa [prefixWord, tailWord_4162884, baseEnd_4162884] using wordTrace_append hprefix tailTrace_4162884
  have hstable : (prefixWord ++ tailWord_4162884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162884).length < 2 ^ (prefixWord ++ tailWord_4162884).sum := by decide
  have hdescent : baseEnd_4162884 < baseStart_4162884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162927 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 6, 4]
def baseStart_4162927 : Nat := 118140960795 + 4162927 * 2 ^ 59
def prefixEnd_4162927 : Nat := 4983230072969 + 3 ^ 40 * 4162927 * 2
def baseEnd_4162927 : Nat := 712527493526513087555851

theorem tailTrace_4162927 : CollatzResearch.WordTrace tailWord_4162927 prefixEnd_4162927 712527493526513087555851 := by
  unfold tailWord_4162927
  simp only [CollatzResearch.WordTrace]
  refine ⟨151834421389433925173391035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101222947592955950115594023 151834421389433925173391035)
  ·
    refine ⟨227751632084150887760086553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151834421389433925173391035 227751632084150887760086553)
    ·
      refine ⟨170813724063113165820064915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227751632084150887760086553 170813724063113165820064915)
      ·
        refine ⟨256220586094669748730097373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170813724063113165820064915 256220586094669748730097373)
        ·
          refine ⟨96082719785501155773786515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256220586094669748730097373 96082719785501155773786515)
          ·
            refine ⟨144124079678251733660679773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96082719785501155773786515 144124079678251733660679773)
            ·
              refine ⟨54046529879344400122754915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144124079678251733660679773 54046529879344400122754915)
              ·
                refine ⟨81069794819016600184132373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54046529879344400122754915 81069794819016600184132373)
                ·
                  refine ⟨3800146632141403133631205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81069794819016600184132373 3800146632141403133631205)
                  ·
                    refine ⟨712527493526513087555851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800146632141403133631205 712527493526513087555851)
                    ·
                      rfl

theorem cell23_4162927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 4].length) (baseStart_4162927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162927 prefixEnd_4162927 := by exact prefixLift 4162927
  have htrace : WordTrace (prefixWord ++ tailWord_4162927) baseStart_4162927 baseEnd_4162927 := by
    simpa [prefixWord, tailWord_4162927, baseEnd_4162927] using wordTrace_append hprefix tailTrace_4162927
  have hstable : (prefixWord ++ tailWord_4162927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162927).length < 2 ^ (prefixWord ++ tailWord_4162927).sum := by decide
  have hdescent : baseEnd_4162927 < baseStart_4162927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162937 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_4162937 : Nat := 118140960795 + 4162937 * 2 ^ 59
def prefixEnd_4162937 : Nat := 4983230072969 + 3 ^ 40 * 4162937 * 2
def baseEnd_4162937 : Nat := 2137587615386084223542507

theorem tailTrace_4162937 : CollatzResearch.WordTrace tailWord_4162937 prefixEnd_4162937 2137587615386084223542507 := by
  unfold tailWord_4162937
  simp only [CollatzResearch.WordTrace]
  refine ⟨151834786119397696881255065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101223190746265131254170043 151834786119397696881255065)
  ·
    refine ⟨113876089589548272660941299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151834786119397696881255065 113876089589548272660941299)
    ·
      refine ⟨170814134384322408991411949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113876089589548272660941299 170814134384322408991411949)
      ·
        refine ⟨64055300394120903371779481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170814134384322408991411949 64055300394120903371779481)
        ·
          refine ⟨48041475295590677528834611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64055300394120903371779481 48041475295590677528834611)
          ·
            refine ⟨72062212943386016293251917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48041475295590677528834611 72062212943386016293251917)
            ·
              refine ⟨27023329853769756109969469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72062212943386016293251917 27023329853769756109969469)
              ·
                refine ⟨10133748695163658541238551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27023329853769756109969469 10133748695163658541238551)
                ·
                  refine ⟨15200623042745487811857827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10133748695163658541238551 15200623042745487811857827)
                  ·
                    refine ⟨22800934564118231717786741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15200623042745487811857827 22800934564118231717786741)
                    ·
                      refine ⟨2137587615386084223542507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22800934564118231717786741 2137587615386084223542507)
                      ·
                        rfl

theorem cell23_4162937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_4162937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162937 prefixEnd_4162937 := by exact prefixLift 4162937
  have htrace : WordTrace (prefixWord ++ tailWord_4162937) baseStart_4162937 baseEnd_4162937 := by
    simpa [prefixWord, tailWord_4162937, baseEnd_4162937] using wordTrace_append hprefix tailTrace_4162937
  have hstable : (prefixWord ++ tailWord_4162937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162937).length < 2 ^ (prefixWord ++ tailWord_4162937).sum := by decide
  have hdescent : baseEnd_4162937 < baseStart_4162937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162945 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_4162945 : Nat := 118140960795 + 4162945 * 2 ^ 59
def prefixEnd_4162945 : Nat := 4983230072969 + 3 ^ 40 * 4162945 * 2
def baseEnd_4162945 : Nat := 2137591723231320192242471

theorem tailTrace_4162945 : CollatzResearch.WordTrace tailWord_4162945 prefixEnd_4162945 2137591723231320192242471 := by
  unfold tailWord_4162945
  simp only [CollatzResearch.WordTrace]
  refine ⟨151835077903368714247546289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101223385268912476165030859 151835077903368714247546289)
  ·
    refine ⟨113876308427526535685659717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151835077903368714247546289 113876308427526535685659717)
    ·
      refine ⟨21351807830161225441061197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113876308427526535685659717 21351807830161225441061197)
      ·
        refine ⟨8006927936310459540397949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21351807830161225441061197 8006927936310459540397949)
        ·
          refine ⟨3002597976116422327649231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8006927936310459540397949 3002597976116422327649231)
          ·
            refine ⟨4503896964174633491473847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002597976116422327649231 4503896964174633491473847)
            ·
              refine ⟨6755845446261950237210771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503896964174633491473847 6755845446261950237210771)
              ·
                refine ⟨10133768169392925355816157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755845446261950237210771 10133768169392925355816157)
                ·
                  refine ⟨3800163063522347008431059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10133768169392925355816157 3800163063522347008431059)
                  ·
                    refine ⟨5700244595283520512646589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3800163063522347008431059 5700244595283520512646589)
                    ·
                      refine ⟨2137591723231320192242471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5700244595283520512646589 2137591723231320192242471)
                      ·
                        rfl

theorem cell23_4162945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_4162945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162945 prefixEnd_4162945 := by exact prefixLift 4162945
  have htrace : WordTrace (prefixWord ++ tailWord_4162945) baseStart_4162945 baseEnd_4162945 := by
    simpa [prefixWord, tailWord_4162945, baseEnd_4162945] using wordTrace_append hprefix tailTrace_4162945
  have hstable : (prefixWord ++ tailWord_4162945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162945).length < 2 ^ (prefixWord ++ tailWord_4162945).sum := by decide
  have hdescent : baseEnd_4162945 < baseStart_4162945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162947 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 6]
def baseStart_4162947 : Nat := 118140960795 + 4162947 * 2 ^ 59
def prefixEnd_4162947 : Nat := 4983230072969 + 3 ^ 40 * 4162947 * 2
def baseEnd_4162947 : Nat := 2137592750192629184417461

theorem tailTrace_4162947 : CollatzResearch.WordTrace tailWord_4162947 prefixEnd_4162947 2137592750192629184417461 := by
  unfold tailWord_4162947
  simp only [CollatzResearch.WordTrace]
  refine ⟨151835150849361468589119095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101223433899574312392746063 151835150849361468589119095)
  ·
    refine ⟨227752726274042202883678643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151835150849361468589119095 227752726274042202883678643)
    ·
      refine ⟨341629089411063304325517965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227752726274042202883678643 341629089411063304325517965)
      ·
        refine ⟨128110908529148739122069237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341629089411063304325517965 128110908529148739122069237)
        ·
          refine ⟨12010397674607694292693991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128110908529148739122069237 12010397674607694292693991)
          ·
            refine ⟨18015596511911541439040987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12010397674607694292693991 18015596511911541439040987)
            ·
              refine ⟨27023394767867312158561481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18015596511911541439040987 27023394767867312158561481)
              ·
                refine ⟨20267546075900484118921111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27023394767867312158561481 20267546075900484118921111)
                ·
                  refine ⟨30401319113850726178381667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20267546075900484118921111 30401319113850726178381667)
                  ·
                    refine ⟨45601978670776089267572501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30401319113850726178381667 45601978670776089267572501)
                    ·
                      refine ⟨2137592750192629184417461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45601978670776089267572501 2137592750192629184417461)
                      ·
                        rfl

theorem cell23_4162947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_4162947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162947 prefixEnd_4162947 := by exact prefixLift 4162947
  have htrace : WordTrace (prefixWord ++ tailWord_4162947) baseStart_4162947 baseEnd_4162947 := by
    simpa [prefixWord, tailWord_4162947, baseEnd_4162947] using wordTrace_append hprefix tailTrace_4162947
  have hstable : (prefixWord ++ tailWord_4162947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162947).length < 2 ^ (prefixWord ++ tailWord_4162947).sum := by decide
  have hdescent : baseEnd_4162947 < baseStart_4162947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162964 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_4162964 : Nat := 118140960795 + 4162964 * 2 ^ 59
def prefixEnd_4162964 : Nat := 4983230072969 + 3 ^ 40 * 4162964 * 2
def baseEnd_4162964 : Nat := 2137601479363755617904883

theorem tailTrace_4162964 : CollatzResearch.WordTrace tailWord_4162964 prefixEnd_4162964 2137601479363755617904883 := by
  unfold tailWord_4162964
  simp only [CollatzResearch.WordTrace]
  refine ⟨75917885445149940246243973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101223847260199920328325297 75917885445149940246243973)
  ·
    refine ⟨14234603520965613796170745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75917885445149940246243973 14234603520965613796170745)
    ·
      refine ⟨10675952640724210347128059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14234603520965613796170745 10675952640724210347128059)
      ·
        refine ⟨16013928961086315520692089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10675952640724210347128059 16013928961086315520692089)
        ·
          refine ⟨12010446720814736640519067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16013928961086315520692089 12010446720814736640519067)
          ·
            refine ⟨18015670081222104960778601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12010446720814736640519067 18015670081222104960778601)
            ·
              refine ⟨13511752560916578720583951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18015670081222104960778601 13511752560916578720583951)
              ·
                refine ⟨20267628841374868080875927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13511752560916578720583951 20267628841374868080875927)
                ·
                  refine ⟨30401443262062302121313891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20267628841374868080875927 30401443262062302121313891)
                  ·
                    refine ⟨45602164893093453181970837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30401443262062302121313891 45602164893093453181970837)
                    ·
                      refine ⟨2137601479363755617904883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45602164893093453181970837 2137601479363755617904883)
                      ·
                        rfl

theorem cell23_4162964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_4162964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162964 prefixEnd_4162964 := by exact prefixLift 4162964
  have htrace : WordTrace (prefixWord ++ tailWord_4162964) baseStart_4162964 baseEnd_4162964 := by
    simpa [prefixWord, tailWord_4162964, baseEnd_4162964] using wordTrace_append hprefix tailTrace_4162964
  have hstable : (prefixWord ++ tailWord_4162964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162964).length < 2 ^ (prefixWord ++ tailWord_4162964).sum := by decide
  have hdescent : baseEnd_4162964 < baseStart_4162964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4162968 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4162968 : Nat := 118140960795 + 4162968 * 2 ^ 59
def prefixEnd_4162968 : Nat := 4983230072969 + 3 ^ 40 * 4162968 * 2
def baseEnd_4162968 : Nat := 2137603533286373602254865

theorem tailTrace_4162968 : CollatzResearch.WordTrace tailWord_4162968 prefixEnd_4162968 2137603533286373602254865 := by
  unfold tailWord_4162968
  simp only [CollatzResearch.WordTrace]
  refine ⟨75917958391142694587816779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101223944521523592783755705 75917958391142694587816779)
  ·
    refine ⟨113876937586714041881725169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75917958391142694587816779 113876937586714041881725169)
    ·
      refine ⟨85407703190035531411293877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113876937586714041881725169 85407703190035531411293877)
      ·
        refine ⟨8006972174065831069808801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85407703190035531411293877 8006972174065831069808801)
        ·
          refine ⟨6005229130549373302356601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8006972174065831069808801 6005229130549373302356601)
          ·
            refine ⟨4503921847912029976767451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6005229130549373302356601 4503921847912029976767451)
            ·
              refine ⟨6755882771868044965151177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503921847912029976767451 6755882771868044965151177)
              ·
                refine ⟨5066912078901033723863383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6755882771868044965151177 5066912078901033723863383)
                ·
                  refine ⟨7600368118351550585795075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5066912078901033723863383 7600368118351550585795075)
                  ·
                    refine ⟨11400552177527325878692613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7600368118351550585795075 11400552177527325878692613)
                    ·
                      refine ⟨2137603533286373602254865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11400552177527325878692613 2137603533286373602254865)
                      ·
                        rfl

theorem cell23_4162968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4162968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4162968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4162968 prefixEnd_4162968 := by exact prefixLift 4162968
  have htrace : WordTrace (prefixWord ++ tailWord_4162968) baseStart_4162968 baseEnd_4162968 := by
    simpa [prefixWord, tailWord_4162968, baseEnd_4162968] using wordTrace_append hprefix tailTrace_4162968
  have hstable : (prefixWord ++ tailWord_4162968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4162968).length < 2 ^ (prefixWord ++ tailWord_4162968).sum := by decide
  have hdescent : baseEnd_4162968 < baseStart_4162968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4162968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163024 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 5, 4, 2]
def baseStart_4163024 : Nat := 118140960795 + 4163024 * 2 ^ 59
def prefixEnd_4163024 : Nat := 4983230072969 + 3 ^ 40 * 4163024 * 2
def baseEnd_4163024 : Nat := 2137632288203025383154607

theorem tailTrace_4163024 : CollatzResearch.WordTrace tailWord_4163024 prefixEnd_4163024 2137632288203025383154607 := by
  unfold tailWord_4163024
  simp only [CollatzResearch.WordTrace]
  refine ⟨75918979635041255369836063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101225306180055007159781417 75918979635041255369836063)
  ·
    refine ⟨113878469452561883054754095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75918979635041255369836063 113878469452561883054754095)
    ·
      refine ⟨170817704178842824582131143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113878469452561883054754095 170817704178842824582131143)
      ·
        refine ⟨256226556268264236873196715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170817704178842824582131143 256226556268264236873196715)
        ·
          refine ⟨384339834402396355309795073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256226556268264236873196715 384339834402396355309795073)
          ·
            refine ⟨288254875801797266482346305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384339834402396355309795073 288254875801797266482346305)
            ·
              refine ⟨216191156851347949861759729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288254875801797266482346305 216191156851347949861759729)
              ·
                refine ⟨162143367638510962396319797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216191156851347949861759729 162143367638510962396319797)
                ·
                  refine ⟨15200940716110402724654981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162143367638510962396319797 15200940716110402724654981)
                  ·
                    refine ⟨2850176384270700510872809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15200940716110402724654981 2850176384270700510872809)
                    ·
                      refine ⟨2137632288203025383154607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850176384270700510872809 2137632288203025383154607)
                      ·
                        rfl

theorem cell23_4163024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 4, 2].length) (baseStart_4163024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163024 prefixEnd_4163024 := by exact prefixLift 4163024
  have htrace : WordTrace (prefixWord ++ tailWord_4163024) baseStart_4163024 baseEnd_4163024 := by
    simpa [prefixWord, tailWord_4163024, baseEnd_4163024] using wordTrace_append hprefix tailTrace_4163024
  have hstable : (prefixWord ++ tailWord_4163024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163024).length < 2 ^ (prefixWord ++ tailWord_4163024).sum := by decide
  have hdescent : baseEnd_4163024 < baseStart_4163024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163041 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_4163041 : Nat := 118140960795 + 4163041 * 2 ^ 59
def prefixEnd_4163041 : Nat := 4983230072969 + 3 ^ 40 * 4163041 * 2
def baseEnd_4163041 : Nat := 2137641017374151816642029

theorem tailTrace_4163041 : CollatzResearch.WordTrace tailWord_4163041 prefixEnd_4163041 2137641017374151816642029 := by
  unfold tailWord_4163041
  simp only [CollatzResearch.WordTrace]
  refine ⟨151838579311020922643040977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101225719540680615095360651 151838579311020922643040977)
  ·
    refine ⟨113878934483265691982280733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151838579311020922643040977 113878934483265691982280733)
    ·
      refine ⟨42704600431224634493355275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113878934483265691982280733 42704600431224634493355275)
      ·
        refine ⟨64056900646836951740032913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42704600431224634493355275 64056900646836951740032913)
        ·
          refine ⟨48042675485127713805024685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64056900646836951740032913 48042675485127713805024685)
          ·
            refine ⟨18016003306922892676884257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48042675485127713805024685 18016003306922892676884257)
            ·
              refine ⟨13512002480192169507663193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18016003306922892676884257 13512002480192169507663193)
              ·
                refine ⟨10134001860144127130747395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13512002480192169507663193 10134001860144127130747395)
                ·
                  refine ⟨15201002790216190696121093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10134001860144127130747395 15201002790216190696121093)
                  ·
                    refine ⟨2850188023165535755522705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15201002790216190696121093 2850188023165535755522705)
                    ·
                      refine ⟨2137641017374151816642029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850188023165535755522705 2137641017374151816642029)
                      ·
                        rfl

theorem cell23_4163041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_4163041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163041 prefixEnd_4163041 := by exact prefixLift 4163041
  have htrace : WordTrace (prefixWord ++ tailWord_4163041) baseStart_4163041 baseEnd_4163041 := by
    simpa [prefixWord, tailWord_4163041, baseEnd_4163041] using wordTrace_append hprefix tailTrace_4163041
  have hstable : (prefixWord ++ tailWord_4163041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163041).length < 2 ^ (prefixWord ++ tailWord_4163041).sum := by decide
  have hdescent : baseEnd_4163041 < baseStart_4163041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163045 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 1, 3, 2]
def baseStart_4163045 : Nat := 118140960795 + 4163045 * 2 ^ 59
def prefixEnd_4163045 : Nat := 4983230072969 + 3 ^ 40 * 4163045 * 2
def baseEnd_4163045 : Nat := 2137643071296769800992011

theorem tailTrace_4163045 : CollatzResearch.WordTrace tailWord_4163045 prefixEnd_4163045 2137643071296769800992011 := by
  unfold tailWord_4163045
  simp only [CollatzResearch.WordTrace]
  refine ⟨151838725203006431326186589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101225816802004287550791059 151838725203006431326186589)
  ·
    refine ⟨56939521951127411747319971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151838725203006431326186589 56939521951127411747319971)
    ·
      refine ⟨85409282926691117620979957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56939521951127411747319971 85409282926691117620979957)
      ·
        refine ⟨8007120274377292276966871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85409282926691117620979957 8007120274377292276966871)
        ·
          refine ⟨12010680411565938415450307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8007120274377292276966871 12010680411565938415450307)
          ·
            refine ⟨18016020617348907623175461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12010680411565938415450307 18016020617348907623175461)
            ·
              refine ⟨3378003865752920179345399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18016020617348907623175461 3378003865752920179345399)
              ·
                refine ⟨5067005798629380269018099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378003865752920179345399 5067005798629380269018099)
                ·
                  refine ⟨7600508697944070403527149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067005798629380269018099 7600508697944070403527149)
                  ·
                    refine ⟨2850190761729026401322681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7600508697944070403527149 2850190761729026401322681)
                    ·
                      refine ⟨2137643071296769800992011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850190761729026401322681 2137643071296769800992011)
                      ·
                        rfl

theorem cell23_4163045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_4163045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163045 prefixEnd_4163045 := by exact prefixLift 4163045
  have htrace : WordTrace (prefixWord ++ tailWord_4163045) baseStart_4163045 baseEnd_4163045 := by
    simpa [prefixWord, tailWord_4163045, baseEnd_4163045] using wordTrace_append hprefix tailTrace_4163045
  have hstable : (prefixWord ++ tailWord_4163045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163045).length < 2 ^ (prefixWord ++ tailWord_4163045).sum := by decide
  have hdescent : baseEnd_4163045 < baseStart_4163045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163054 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4163054 : Nat := 118140960795 + 4163054 * 2 ^ 59
def prefixEnd_4163054 : Nat := 4983230072969 + 3 ^ 40 * 4163054 * 2
def baseEnd_4163054 : Nat := 2137647692622660265779469

theorem tailTrace_4163054 : CollatzResearch.WordTrace tailWord_4163054 prefixEnd_4163054 2137647692622660265779469 := by
  unfold tailWord_4163054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18979881682496728232908027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101226035639982550575509477 18979881682496728232908027)
  ·
    refine ⟨28469822523745092349362041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18979881682496728232908027 28469822523745092349362041)
    ·
      refine ⟨21352366892808819262021531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28469822523745092349362041 21352366892808819262021531)
      ·
        refine ⟨32028550339213228893032297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21352366892808819262021531 32028550339213228893032297)
        ·
          refine ⟨24021412754409921669774223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32028550339213228893032297 24021412754409921669774223)
          ·
            refine ⟨36032119131614882504661335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24021412754409921669774223 36032119131614882504661335)
            ·
              refine ⟨54048178697422323756992003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36032119131614882504661335 54048178697422323756992003)
              ·
                refine ⟨81072268046133485635488005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54048178697422323756992003 81072268046133485635488005)
                ·
                  refine ⟨15201050258650028556654001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81072268046133485635488005 15201050258650028556654001)
                  ·
                    refine ⟨11400787693987521417490501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15201050258650028556654001 11400787693987521417490501)
                    ·
                      refine ⟨2137647692622660265779469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11400787693987521417490501 2137647692622660265779469)
                      ·
                        rfl

theorem cell23_4163054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4163054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163054 prefixEnd_4163054 := by exact prefixLift 4163054
  have htrace : WordTrace (prefixWord ++ tailWord_4163054) baseStart_4163054 baseEnd_4163054 := by
    simpa [prefixWord, tailWord_4163054, baseEnd_4163054] using wordTrace_append hprefix tailTrace_4163054
  have hstable : (prefixWord ++ tailWord_4163054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163054).length < 2 ^ (prefixWord ++ tailWord_4163054).sum := by decide
  have hdescent : baseEnd_4163054 < baseStart_4163054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163064 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 7]
def baseStart_4163064 : Nat := 118140960795 + 4163064 * 2 ^ 59
def prefixEnd_4163064 : Nat := 4983230072969 + 3 ^ 40 * 4163064 * 2
def baseEnd_4163064 : Nat := 237516980825467247406047

theorem tailTrace_4163064 : CollatzResearch.WordTrace tailWord_4163064 prefixEnd_4163064 237516980825467247406047 := by
  unfold tailWord_4163064
  simp only [CollatzResearch.WordTrace]
  refine ⟨75919709094968798785564123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101226278793291731714085497 75919709094968798785564123)
  ·
    refine ⟨113879563642453198178346185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75919709094968798785564123 113879563642453198178346185)
    ·
      refine ⟨85409672731839898633759639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113879563642453198178346185 85409672731839898633759639)
      ·
        refine ⟨128114509097759847950639459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85409672731839898633759639 128114509097759847950639459)
        ·
          refine ⟨192171763646639771925959189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128114509097759847950639459 192171763646639771925959189)
          ·
            refine ⟨9008051420936239309029337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192171763646639771925959189 9008051420936239309029337)
            ·
              refine ⟨6756038565702179481772003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9008051420936239309029337 6756038565702179481772003)
              ·
                refine ⟨10134057848553269222658005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6756038565702179481772003 10134057848553269222658005)
                ·
                  refine ⟨237516980825467247406047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10134057848553269222658005 237516980825467247406047)
                  ·
                    rfl

theorem cell23_4163064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 7].length) (baseStart_4163064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163064 prefixEnd_4163064 := by exact prefixLift 4163064
  have htrace : WordTrace (prefixWord ++ tailWord_4163064) baseStart_4163064 baseEnd_4163064 := by
    simpa [prefixWord, tailWord_4163064, baseEnd_4163064] using wordTrace_append hprefix tailTrace_4163064
  have hstable : (prefixWord ++ tailWord_4163064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163064).length < 2 ^ (prefixWord ++ tailWord_4163064).sum := by decide
  have hdescent : baseEnd_4163064 < baseStart_4163064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163126 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_4163126 : Nat := 118140960795 + 4163126 * 2 ^ 59
def prefixEnd_4163126 : Nat := 4983230072969 + 3 ^ 40 * 4163126 * 2
def baseEnd_4163126 : Nat := 2137684663229783984079139

theorem tailTrace_4163126 : CollatzResearch.WordTrace tailWord_4163126 prefixEnd_4163126 2137684663229783984079139 := by
  unfold tailWord_4163126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490104969732061384992827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101227786343808654773256821 9490104969732061384992827)
  ·
    refine ⟨14235157454598092077489241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9490104969732061384992827 14235157454598092077489241)
    ·
      refine ⟨10676368090948569058116931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14235157454598092077489241 10676368090948569058116931)
      ·
        refine ⟨16014552136422853587175397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10676368090948569058116931 16014552136422853587175397)
        ·
          refine ⟨3002728525579285047595387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16014552136422853587175397 3002728525579285047595387)
          ·
            refine ⟨4504092788368927571393081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002728525579285047595387 4504092788368927571393081)
            ·
              refine ⟨3378069591276695678544811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4504092788368927571393081 3378069591276695678544811)
              ·
                refine ⟨5067104386915043517817217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378069591276695678544811 5067104386915043517817217)
                ·
                  refine ⟨3800328290186282638362913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5067104386915043517817217 3800328290186282638362913)
                  ·
                    refine ⟨2850246217639711978772185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3800328290186282638362913 2850246217639711978772185)
                    ·
                      refine ⟨2137684663229783984079139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850246217639711978772185 2137684663229783984079139)
                      ·
                        rfl

theorem cell23_4163126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_4163126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163126 prefixEnd_4163126 := by exact prefixLift 4163126
  have htrace : WordTrace (prefixWord ++ tailWord_4163126) baseStart_4163126 baseEnd_4163126 := by
    simpa [prefixWord, tailWord_4163126, baseEnd_4163126] using wordTrace_append hprefix tailTrace_4163126
  have hstable : (prefixWord ++ tailWord_4163126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163126).length < 2 ^ (prefixWord ++ tailWord_4163126).sum := by decide
  have hdescent : baseEnd_4163126 < baseStart_4163126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163171 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 6]
def baseStart_4163171 : Nat := 118140960795 + 4163171 * 2 ^ 59
def prefixEnd_4163171 : Nat := 4983230072969 + 3 ^ 40 * 4163171 * 2
def baseEnd_4163171 : Nat := 237523085539915145335159

theorem tailTrace_4163171 : CollatzResearch.WordTrace tailWord_4163171 prefixEnd_4163171 237523085539915145335159 := by
  unfold tailWord_4163171
  simp only [CollatzResearch.WordTrace]
  refine ⟨151843320800549954845273367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101228880533699969896848911 151843320800549954845273367)
  ·
    refine ⟨227764981200824932267910051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151843320800549954845273367 227764981200824932267910051)
    ·
      refine ⟨341647471801237398401865077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227764981200824932267910051 341647471801237398401865077)
      ·
        refine ⟨32029450481366006100174851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 341647471801237398401865077 32029450481366006100174851)
        ·
          refine ⟨48044175722049009150262277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32029450481366006100174851 48044175722049009150262277)
          ·
            refine ⟨9008282947884189215674177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48044175722049009150262277 9008282947884189215674177)
            ·
              refine ⟨6756212210913141911755633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9008282947884189215674177 6756212210913141911755633)
              ·
                refine ⟨5067159158184856433816725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6756212210913141911755633 5067159158184856433816725)
                ·
                  refine ⟨237523085539915145335159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5067159158184856433816725 237523085539915145335159)
                  ·
                    rfl

theorem cell23_4163171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 6].length) (baseStart_4163171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163171 prefixEnd_4163171 := by exact prefixLift 4163171
  have htrace : WordTrace (prefixWord ++ tailWord_4163171) baseStart_4163171 baseEnd_4163171 := by
    simpa [prefixWord, tailWord_4163171, baseEnd_4163171] using wordTrace_append hprefix tailTrace_4163171
  have hstable : (prefixWord ++ tailWord_4163171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163171).length < 2 ^ (prefixWord ++ tailWord_4163171).sum := by decide
  have hdescent : baseEnd_4163171 < baseStart_4163171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163175 : List Nat := [1, 1, 5, 1, 1, 1, 6, 2, 1, 4]
def baseStart_4163175 : Nat := 118140960795 + 4163175 * 2 ^ 59
def prefixEnd_4163175 : Nat := 4983230072969 + 3 ^ 40 * 4163175 * 2
def baseEnd_4163175 : Nat := 712569941260618097455471

theorem tailTrace_4163175 : CollatzResearch.WordTrace tailWord_4163175 prefixEnd_4163175 712569941260618097455471 := by
  unfold tailWord_4163175
  simp only [CollatzResearch.WordTrace]
  refine ⟨151843466692535463528418979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101228977795023642352279319 151843466692535463528418979)
  ·
    refine ⟨227765200038803195292628469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151843466692535463528418979 227765200038803195292628469)
    ·
      refine ⟨21352987503637799558683919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227765200038803195292628469 21352987503637799558683919)
      ·
        refine ⟨32029481255456699338025879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21352987503637799558683919 32029481255456699338025879)
        ·
          refine ⟨48044221883185049007038819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32029481255456699338025879 48044221883185049007038819)
          ·
            refine ⟨72066332824777573510558229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48044221883185049007038819 72066332824777573510558229)
            ·
              refine ⟨3378109351161448758307417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72066332824777573510558229 3378109351161448758307417)
              ·
                refine ⟨2533582013371086568730563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378109351161448758307417 2533582013371086568730563)
                ·
                  refine ⟨3800373020056629853095845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533582013371086568730563 3800373020056629853095845)
                  ·
                    refine ⟨712569941260618097455471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800373020056629853095845 712569941260618097455471)
                    ·
                      rfl

theorem cell23_4163175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_4163175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163175 prefixEnd_4163175 := by exact prefixLift 4163175
  have htrace : WordTrace (prefixWord ++ tailWord_4163175) baseStart_4163175 baseEnd_4163175 := by
    simpa [prefixWord, tailWord_4163175, baseEnd_4163175] using wordTrace_append hprefix tailTrace_4163175
  have hstable : (prefixWord ++ tailWord_4163175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163175).length < 2 ^ (prefixWord ++ tailWord_4163175).sum := by decide
  have hdescent : baseEnd_4163175 < baseStart_4163175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163191 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 1, 5, 2]
def baseStart_4163191 : Nat := 118140960795 + 4163191 * 2 ^ 59
def prefixEnd_4163191 : Nat := 4983230072969 + 3 ^ 40 * 4163191 * 2
def baseEnd_4163191 : Nat := 2137718039472326229766339

theorem tailTrace_4163191 : CollatzResearch.WordTrace tailWord_4163191 prefixEnd_4163191 2137718039472326229766339 := by
  unfold tailWord_4163191
  simp only [CollatzResearch.WordTrace]
  refine ⟨151844050260477498261001427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101229366840318332174000951 151844050260477498261001427)
  ·
    refine ⟨227766075390716247391502141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151844050260477498261001427 227766075390716247391502141)
    ·
      refine ⟨85412278271518592771813303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227766075390716247391502141 85412278271518592771813303)
      ·
        refine ⟨128118417407277889157719955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85412278271518592771813303 128118417407277889157719955)
        ·
          refine ⟨192177626110916833736579933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128118417407277889157719955 192177626110916833736579933)
          ·
            refine ⟨72066609791593812651217475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192177626110916833736579933 72066609791593812651217475)
            ·
              refine ⟨108099914687390718976826213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72066609791593812651217475 108099914687390718976826213)
              ·
                refine ⟨20268734003885759808154915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108099914687390718976826213 20268734003885759808154915)
                ·
                  refine ⟨30403101005828639712232373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20268734003885759808154915 30403101005828639712232373)
                  ·
                    refine ⟨2850290719296434973021785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30403101005828639712232373 2850290719296434973021785)
                    ·
                      refine ⟨2137718039472326229766339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850290719296434973021785 2137718039472326229766339)
                      ·
                        rfl

theorem cell23_4163191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_4163191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163191 prefixEnd_4163191 := by exact prefixLift 4163191
  have htrace : WordTrace (prefixWord ++ tailWord_4163191) baseStart_4163191 baseEnd_4163191 := by
    simpa [prefixWord, tailWord_4163191, baseEnd_4163191] using wordTrace_append hprefix tailTrace_4163191
  have hstable : (prefixWord ++ tailWord_4163191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163191).length < 2 ^ (prefixWord ++ tailWord_4163191).sum := by decide
  have hdescent : baseEnd_4163191 < baseStart_4163191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163201 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4163201 : Nat := 118140960795 + 4163201 * 2 ^ 59
def prefixEnd_4163201 : Nat := 4983230072969 + 3 ^ 40 * 4163201 * 2
def baseEnd_4163201 : Nat := 712574391426290396880431

theorem tailTrace_4163201 : CollatzResearch.WordTrace tailWord_4163201 prefixEnd_4163201 712574391426290396880431 := by
  unfold tailWord_4163201
  simp only [CollatzResearch.WordTrace]
  refine ⟨151844414990441269968865457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101229609993627513312576971 151844414990441269968865457)
  ·
    refine ⟨113883311242830952476649093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151844414990441269968865457 113883311242830952476649093)
    ·
      refine ⟨21353120858030803589371705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113883311242830952476649093 21353120858030803589371705)
      ·
        refine ⟨16014840643523102692028779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21353120858030803589371705 16014840643523102692028779)
        ·
          refine ⟨24022260965284654038043169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16014840643523102692028779 24022260965284654038043169)
          ·
            refine ⟨18016695723963490528532377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24022260965284654038043169 18016695723963490528532377)
            ·
              refine ⟨13512521792972617896399283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18016695723963490528532377 13512521792972617896399283)
              ·
                refine ⟨20268782689458926844598925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13512521792972617896399283 20268782689458926844598925)
                ·
                  refine ⟨7600793508547097566724597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20268782689458926844598925 7600793508547097566724597)
                  ·
                    refine ⟨712574391426290396880431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7600793508547097566724597 712574391426290396880431)
                    ·
                      rfl

theorem cell23_4163201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4163201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163201 prefixEnd_4163201 := by exact prefixLift 4163201
  have htrace : WordTrace (prefixWord ++ tailWord_4163201) baseStart_4163201 baseEnd_4163201 := by
    simpa [prefixWord, tailWord_4163201, baseEnd_4163201] using wordTrace_append hprefix tailTrace_4163201
  have hstable : (prefixWord ++ tailWord_4163201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163201).length < 2 ^ (prefixWord ++ tailWord_4163201).sum := by decide
  have hdescent : baseEnd_4163201 < baseStart_4163201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163221 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_4163221 : Nat := 118140960795 + 4163221 * 2 ^ 59
def prefixEnd_4163221 : Nat := 4983230072969 + 3 ^ 40 * 4163221 * 2
def baseEnd_4163221 : Nat := 2137733443891961112391201

theorem tailTrace_4163221 : CollatzResearch.WordTrace tailWord_4163221 prefixEnd_4163221 2137733443891961112391201 := by
  unfold tailWord_4163221
  simp only [CollatzResearch.WordTrace]
  refine ⟨151845144450368813384593517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101230096300245875589729011 151845144450368813384593517)
  ·
    refine ⟨56941929168888305019222569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151845144450368813384593517 56941929168888305019222569)
    ·
      refine ⟨42706446876666228764416927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56941929168888305019222569 42706446876666228764416927)
      ·
        refine ⟨64059670314999343146625391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42706446876666228764416927 64059670314999343146625391)
        ·
          refine ⟨96089505472499014719938087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64059670314999343146625391 96089505472499014719938087)
          ·
            refine ⟨144134258208748522079907131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96089505472499014719938087 144134258208748522079907131)
            ·
              refine ⟨216201387313122783119860697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144134258208748522079907131 216201387313122783119860697)
              ·
                refine ⟨162151040484842087339895523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216201387313122783119860697 162151040484842087339895523)
                ·
                  refine ⟨243226560727263131009843285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162151040484842087339895523 243226560727263131009843285)
                  ·
                    refine ⟨2850311258522614816521601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 243226560727263131009843285 2850311258522614816521601)
                    ·
                      refine ⟨2137733443891961112391201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850311258522614816521601 2137733443891961112391201)
                      ·
                        rfl

theorem cell23_4163221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_4163221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163221 prefixEnd_4163221 := by exact prefixLift 4163221
  have htrace : WordTrace (prefixWord ++ tailWord_4163221) baseStart_4163221 baseEnd_4163221 := by
    simpa [prefixWord, tailWord_4163221, baseEnd_4163221] using wordTrace_append hprefix tailTrace_4163221
  have hstable : (prefixWord ++ tailWord_4163221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163221).length < 2 ^ (prefixWord ++ tailWord_4163221).sum := by decide
  have hdescent : baseEnd_4163221 < baseStart_4163221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163255 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 3, 2, 2]
def baseStart_4163255 : Nat := 118140960795 + 4163255 * 2 ^ 59
def prefixEnd_4163255 : Nat := 4983230072969 + 3 ^ 40 * 4163255 * 2
def baseEnd_4163255 : Nat := 2137750902234213979366045

theorem tailTrace_4163255 : CollatzResearch.WordTrace tailWord_4163255 prefixEnd_4163255 2137750902234213979366045 := by
  unfold tailWord_4163255
  simp only [CollatzResearch.WordTrace]
  refine ⟨151846384532245637191331219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101230923021497091460887479 151846384532245637191331219)
  ·
    refine ⟨227769576798368455786996829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151846384532245637191331219 227769576798368455786996829)
    ·
      refine ⟨85413591299388170920123811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227769576798368455786996829 85413591299388170920123811)
      ·
        refine ⟨128120386949082256380185717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85413591299388170920123811 128120386949082256380185717)
        ·
          refine ⟨12011286276476461535642411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128120386949082256380185717 12011286276476461535642411)
          ·
            refine ⟨18016929414714692303463617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12011286276476461535642411 18016929414714692303463617)
            ·
              refine ⟨13512697061036019227597713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18016929414714692303463617 13512697061036019227597713)
              ·
                refine ⟨10134522795777014420698285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13512697061036019227597713 10134522795777014420698285)
                ·
                  refine ⟨3800446048416380407761857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10134522795777014420698285 3800446048416380407761857)
                  ·
                    refine ⟨2850334536312285305821393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3800446048416380407761857 2850334536312285305821393)
                    ·
                      refine ⟨2137750902234213979366045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850334536312285305821393 2137750902234213979366045)
                      ·
                        rfl

theorem cell23_4163255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_4163255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163255 prefixEnd_4163255 := by exact prefixLift 4163255
  have htrace : WordTrace (prefixWord ++ tailWord_4163255) baseStart_4163255 baseEnd_4163255 := by
    simpa [prefixWord, tailWord_4163255, baseEnd_4163255] using wordTrace_append hprefix tailTrace_4163255
  have hstable : (prefixWord ++ tailWord_4163255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163255).length < 2 ^ (prefixWord ++ tailWord_4163255).sum := by decide
  have hdescent : baseEnd_4163255 < baseStart_4163255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163258 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3]
def baseStart_4163258 : Nat := 118140960795 + 4163258 * 2 ^ 59
def prefixEnd_4163258 : Nat := 4983230072969 + 3 ^ 40 * 4163258 * 2
def baseEnd_4163258 : Nat := 2137752442676177467628531

theorem tailTrace_4163258 : CollatzResearch.WordTrace tailWord_4163258 prefixEnd_4163258 2137752442676177467628531 := by
  unfold tailWord_4163258
  simp only [CollatzResearch.WordTrace]
  refine ⟨37961623487808692175922607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101230995967489845802460285 37961623487808692175922607)
  ·
    refine ⟨56942435231713038263883911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37961623487808692175922607 56942435231713038263883911)
    ·
      refine ⟨85413652847569557395825867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56942435231713038263883911 85413652847569557395825867)
      ·
        refine ⟨128120479271354336093738801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85413652847569557395825867 128120479271354336093738801)
        ·
          refine ⟨96090359453515752070304101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128120479271354336093738801 96090359453515752070304101)
          ·
            refine ⟨18016942397534203513182019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96090359453515752070304101 18016942397534203513182019)
            ·
              refine ⟨27025413596301305269773029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18016942397534203513182019 27025413596301305269773029)
              ·
                refine ⟨5067265049306494738082443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27025413596301305269773029 5067265049306494738082443)
                ·
                  refine ⟨7600897573959742107123665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067265049306494738082443 7600897573959742107123665)
                  ·
                    refine ⟨5700673180469806580342749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7600897573959742107123665 5700673180469806580342749)
                    ·
                      refine ⟨2137752442676177467628531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5700673180469806580342749 2137752442676177467628531)
                      ·
                        rfl

theorem cell23_4163258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_4163258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163258 prefixEnd_4163258 := by exact prefixLift 4163258
  have htrace : WordTrace (prefixWord ++ tailWord_4163258) baseStart_4163258 baseEnd_4163258 := by
    simpa [prefixWord, tailWord_4163258, baseEnd_4163258] using wordTrace_append hprefix tailTrace_4163258
  have hstable : (prefixWord ++ tailWord_4163258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163258).length < 2 ^ (prefixWord ++ tailWord_4163258).sum := by decide
  have hdescent : baseEnd_4163258 < baseStart_4163258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163271 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_4163271 : Nat := 118140960795 + 4163271 * 2 ^ 59
def prefixEnd_4163271 : Nat := 4983230072969 + 3 ^ 40 * 4163271 * 2
def baseEnd_4163271 : Nat := 2137759117924685916765971

theorem tailTrace_4163271 : CollatzResearch.WordTrace tailWord_4163271 prefixEnd_4163271 2137759117924685916765971 := by
  unfold tailWord_4163271
  simp only [CollatzResearch.WordTrace]
  refine ⟨151846968100187671923913667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101231312066791781282609111 151846968100187671923913667)
  ·
    refine ⟨227770452150281507885870501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151846968100187671923913667 227770452150281507885870501)
    ·
      refine ⟨42706959778177782728600719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227770452150281507885870501 42706959778177782728600719)
      ·
        refine ⟨64060439667266674092901079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42706959778177782728600719 64060439667266674092901079)
        ·
          refine ⟨96090659500900011139351619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64060439667266674092901079 96090659500900011139351619)
          ·
            refine ⟨144135989251350016709027429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96090659500900011139351619 144135989251350016709027429)
            ·
              refine ⟨27025497984628128132942643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144135989251350016709027429 27025497984628128132942643)
              ·
                refine ⟨40538246976942192199413965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27025497984628128132942643 40538246976942192199413965)
                ·
                  refine ⟨15201842616353322074780237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40538246976942192199413965 15201842616353322074780237)
                  ·
                    refine ⟨5700690981132495778042589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15201842616353322074780237 5700690981132495778042589)
                    ·
                      refine ⟨2137759117924685916765971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5700690981132495778042589 2137759117924685916765971)
                      ·
                        rfl

theorem cell23_4163271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_4163271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163271 prefixEnd_4163271 := by exact prefixLift 4163271
  have htrace : WordTrace (prefixWord ++ tailWord_4163271) baseStart_4163271 baseEnd_4163271 := by
    simpa [prefixWord, tailWord_4163271, baseEnd_4163271] using wordTrace_append hprefix tailTrace_4163271
  have hstable : (prefixWord ++ tailWord_4163271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163271).length < 2 ^ (prefixWord ++ tailWord_4163271).sum := by decide
  have hdescent : baseEnd_4163271 < baseStart_4163271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163288 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 4, 1, 3]
def baseStart_4163288 : Nat := 118140960795 + 4163288 * 2 ^ 59
def prefixEnd_4163288 : Nat := 4983230072969 + 3 ^ 40 * 4163288 * 2
def baseEnd_4163288 : Nat := 2137767847095812350253393

theorem tailTrace_4163288 : CollatzResearch.WordTrace tailWord_4163288 prefixEnd_4163288 2137767847095812350253393 := by
  unfold tailWord_4163288
  simp only [CollatzResearch.WordTrace]
  refine ⟨75923794070563041913641259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101231725427417389218188345 75923794070563041913641259)
  ·
    refine ⟨113885691105844562870461889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75923794070563041913641259 113885691105844562870461889)
    ·
      refine ⟨85414268329383422152846417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113885691105844562870461889 85414268329383422152846417)
      ·
        refine ⟨64060701247037566614634813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85414268329383422152846417 64060701247037566614634813)
        ·
          refine ⟨24022762967639087480488055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64060701247037566614634813 24022762967639087480488055)
          ·
            refine ⟨36034144451458631220732083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24022762967639087480488055 36034144451458631220732083)
            ·
              refine ⟨54051216677187946831098125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36034144451458631220732083 54051216677187946831098125)
              ·
                refine ⟨20269206253945480061661797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54051216677187946831098125 20269206253945480061661797)
                ·
                  refine ⟨3800476172614777511561587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20269206253945480061661797 3800476172614777511561587)
                  ·
                    refine ⟨5700714258922166267342381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3800476172614777511561587 5700714258922166267342381)
                    ·
                      refine ⟨2137767847095812350253393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5700714258922166267342381 2137767847095812350253393)
                      ·
                        rfl

theorem cell23_4163288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_4163288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163288 prefixEnd_4163288 := by exact prefixLift 4163288
  have htrace : WordTrace (prefixWord ++ tailWord_4163288) baseStart_4163288 baseEnd_4163288 := by
    simpa [prefixWord, tailWord_4163288, baseEnd_4163288] using wordTrace_append hprefix tailTrace_4163288
  have hstable : (prefixWord ++ tailWord_4163288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163288).length < 2 ^ (prefixWord ++ tailWord_4163288).sum := by decide
  have hdescent : baseEnd_4163288 < baseStart_4163288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163289 : List Nat := [1, 2, 1, 2, 3, 4, 3, 2, 1, 2, 2]
def baseStart_4163289 : Nat := 118140960795 + 4163289 * 2 ^ 59
def prefixEnd_4163289 : Nat := 4983230072969 + 3 ^ 40 * 4163289 * 2
def baseEnd_4163289 : Nat := 2137768360576466846340889

theorem tailTrace_4163289 : CollatzResearch.WordTrace tailWord_4163289 prefixEnd_4163289 2137768360576466846340889 := by
  unfold tailWord_4163289
  simp only [CollatzResearch.WordTrace]
  refine ⟨151847624614122460998068921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101231749742748307332045947 151847624614122460998068921)
  ·
    refine ⟨113885718460591845748551691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151847624614122460998068921 113885718460591845748551691)
    ·
      refine ⟨170828577690887768622827537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113885718460591845748551691 170828577690887768622827537)
      ·
        refine ⟨128121433268165826467120653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170828577690887768622827537 128121433268165826467120653)
        ·
          refine ⟨48045537475562184925170245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128121433268165826467120653 48045537475562184925170245)
          ·
            refine ⟨9008538276667909673469421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48045537475562184925170245 9008538276667909673469421)
            ·
              refine ⟨3378201853750466127551033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9008538276667909673469421 3378201853750466127551033)
              ·
                refine ⟨2533651390312849595663275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378201853750466127551033 2533651390312849595663275)
                ·
                  refine ⟨3800477085469274393494913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533651390312849595663275 3800477085469274393494913)
                  ·
                    refine ⟨2850357814101955795121185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3800477085469274393494913 2850357814101955795121185)
                    ·
                      refine ⟨2137768360576466846340889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850357814101955795121185 2137768360576466846340889)
                      ·
                        rfl

theorem cell23_4163289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 2, 2].length) (baseStart_4163289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163289 prefixEnd_4163289 := by exact prefixLift 4163289
  have htrace : WordTrace (prefixWord ++ tailWord_4163289) baseStart_4163289 baseEnd_4163289 := by
    simpa [prefixWord, tailWord_4163289, baseEnd_4163289] using wordTrace_append hprefix tailTrace_4163289
  have hstable : (prefixWord ++ tailWord_4163289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163289).length < 2 ^ (prefixWord ++ tailWord_4163289).sum := by decide
  have hdescent : baseEnd_4163289 < baseStart_4163289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163299 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 2, 4]
def baseStart_4163299 : Nat := 118140960795 + 4163299 * 2 ^ 59
def prefixEnd_4163299 : Nat := 4983230072969 + 3 ^ 40 * 4163299 * 2
def baseEnd_4163299 : Nat := 712591165127670602405281

theorem tailTrace_4163299 : CollatzResearch.WordTrace tailWord_4163299 prefixEnd_4163299 712591165127670602405281 := by
  unfold tailWord_4163299
  simp only [CollatzResearch.WordTrace]
  refine ⟨151847989344086232705932951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101231992896057488470621967 151847989344086232705932951)
  ·
    refine ⟨227771984016129349058899427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151847989344086232705932951 227771984016129349058899427)
    ·
      refine ⟨341657976024194023588349141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227771984016129349058899427 341657976024194023588349141)
      ·
        refine ⟨8007608813067047427851933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 341657976024194023588349141 8007608813067047427851933)
        ·
          refine ⟨3002853304900142785444475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8007608813067047427851933 3002853304900142785444475)
          ·
            refine ⟨4504279957350214178166713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002853304900142785444475 4504279957350214178166713)
            ·
              refine ⟨3378209968012660633625035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4504279957350214178166713 3378209968012660633625035)
              ·
                refine ⟨5067314952018990950437553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378209968012660633625035 5067314952018990950437553)
                ·
                  refine ⟨3800486214014243212828165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5067314952018990950437553 3800486214014243212828165)
                  ·
                    refine ⟨712591165127670602405281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800486214014243212828165 712591165127670602405281)
                    ·
                      rfl

theorem cell23_4163299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 4].length) (baseStart_4163299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163299 prefixEnd_4163299 := by exact prefixLift 4163299
  have htrace : WordTrace (prefixWord ++ tailWord_4163299) baseStart_4163299 baseEnd_4163299 := by
    simpa [prefixWord, tailWord_4163299, baseEnd_4163299] using wordTrace_append hprefix tailTrace_4163299
  have hstable : (prefixWord ++ tailWord_4163299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163299).length < 2 ^ (prefixWord ++ tailWord_4163299).sum := by decide
  have hdescent : baseEnd_4163299 < baseStart_4163299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163315 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 1, 3, 2]
def baseStart_4163315 : Nat := 118140960795 + 4163315 * 2 ^ 59
def prefixEnd_4163315 : Nat := 4983230072969 + 3 ^ 40 * 4163315 * 2
def baseEnd_4163315 : Nat := 2137781711073483744615769

theorem tailTrace_4163315 : CollatzResearch.WordTrace tailWord_4163315 prefixEnd_4163315 2137781711073483744615769 := by
  unfold tailWord_4163315
  simp only [CollatzResearch.WordTrace]
  refine ⟨151848572912028267438515399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101232381941352178292343599 151848572912028267438515399)
  ·
    refine ⟨227772859368042401157773099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151848572912028267438515399 227772859368042401157773099)
    ·
      refine ⟨341659289052063601736659649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227772859368042401157773099 341659289052063601736659649)
      ·
        refine ⟨256244466789047701302494737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341659289052063601736659649 256244466789047701302494737)
        ·
          refine ⟨192183350091785775976871053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256244466789047701302494737 192183350091785775976871053)
          ·
            refine ⟨72068756284419665991326645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192183350091785775976871053 72068756284419665991326645)
            ·
              refine ⟨6756445901664343686686873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72068756284419665991326645 6756445901664343686686873)
              ·
                refine ⟨5067334426248257765015155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6756445901664343686686873 5067334426248257765015155)
                ·
                  refine ⟨7601001639372386647522733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067334426248257765015155 7601001639372386647522733)
                  ·
                    refine ⟨2850375614764644992821025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7601001639372386647522733 2850375614764644992821025)
                    ·
                      refine ⟨2137781711073483744615769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850375614764644992821025 2137781711073483744615769)
                      ·
                        rfl

theorem cell23_4163315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 3, 2].length) (baseStart_4163315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163315 prefixEnd_4163315 := by exact prefixLift 4163315
  have htrace : WordTrace (prefixWord ++ tailWord_4163315) baseStart_4163315 baseEnd_4163315 := by
    simpa [prefixWord, tailWord_4163315, baseEnd_4163315] using wordTrace_append hprefix tailTrace_4163315
  have hstable : (prefixWord ++ tailWord_4163315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163315).length < 2 ^ (prefixWord ++ tailWord_4163315).sum := by decide
  have hdescent : baseEnd_4163315 < baseStart_4163315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163328 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 1, 4, 2]
def baseStart_4163328 : Nat := 118140960795 + 4163328 * 2 ^ 59
def prefixEnd_4163328 : Nat := 4983230072969 + 3 ^ 40 * 4163328 * 2
def baseEnd_4163328 : Nat := 2137788386321992193753209

theorem tailTrace_4163328 : CollatzResearch.WordTrace tailWord_4163328 prefixEnd_4163328 2137788386321992193753209 := by
  unfold tailWord_4163328
  simp only [CollatzResearch.WordTrace]
  refine ⟨75924523530490585329369319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101232698040654113772492425 75924523530490585329369319)
  ·
    refine ⟨113886785295735877994053979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75924523530490585329369319 113886785295735877994053979)
    ·
      refine ⟨170830177943603816991080969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113886785295735877994053979 170830177943603816991080969)
      ·
        refine ⟨128122633457702862743310727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170830177943603816991080969 128122633457702862743310727)
        ·
          refine ⟨192183950186554294114966091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128122633457702862743310727 192183950186554294114966091)
          ·
            refine ⟨288275925279831441172449137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192183950186554294114966091 288275925279831441172449137)
            ·
              refine ⟨216206943959873580879336853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288275925279831441172449137 216206943959873580879336853)
              ·
                refine ⟨10134700498119074103718915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 216206943959873580879336853 10134700498119074103718915)
                ·
                  refine ⟨15202050747178611155578373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10134700498119074103718915 15202050747178611155578373)
                  ·
                    refine ⟨2850384515095989591670945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15202050747178611155578373 2850384515095989591670945)
                    ·
                      refine ⟨2137788386321992193753209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850384515095989591670945 2137788386321992193753209)
                      ·
                        rfl

theorem cell23_4163328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_4163328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163328 prefixEnd_4163328 := by exact prefixLift 4163328
  have htrace : WordTrace (prefixWord ++ tailWord_4163328) baseStart_4163328 baseEnd_4163328 := by
    simpa [prefixWord, tailWord_4163328, baseEnd_4163328] using wordTrace_append hprefix tailTrace_4163328
  have hstable : (prefixWord ++ tailWord_4163328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163328).length < 2 ^ (prefixWord ++ tailWord_4163328).sum := by decide
  have hdescent : baseEnd_4163328 < baseStart_4163328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163331 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 5]
def baseStart_4163331 : Nat := 118140960795 + 4163331 * 2 ^ 59
def prefixEnd_4163331 : Nat := 4983230072969 + 3 ^ 40 * 4163331 * 2
def baseEnd_4163331 : Nat := 2137789926763955682015695

theorem tailTrace_4163331 : CollatzResearch.WordTrace tailWord_4163331 prefixEnd_4163331 2137789926763955682015695 := by
  unfold tailWord_4163331
  simp only [CollatzResearch.WordTrace]
  refine ⟨151849156479970302171097847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101232770986646868114065231 151849156479970302171097847)
  ·
    refine ⟨227773734719955453256646771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151849156479970302171097847 227773734719955453256646771)
    ·
      refine ⟨341660602079933179884970157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227773734719955453256646771 341660602079933179884970157)
      ·
        refine ⟨128122725779974942456863809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341660602079933179884970157 128122725779974942456863809)
        ·
          refine ⟨96092044334981206842647857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128122725779974942456863809 96092044334981206842647857)
          ·
            refine ⟨72069033251235905131985893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96092044334981206842647857 72069033251235905131985893)
            ·
              refine ⟨13512943734606732212247355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72069033251235905131985893 13512943734606732212247355)
              ·
                refine ⟨20269415601910098318371033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13512943734606732212247355 20269415601910098318371033)
                ·
                  refine ⟨15202061701432573738778275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20269415601910098318371033 15202061701432573738778275)
                  ·
                    refine ⟨22803092552148860608167413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15202061701432573738778275 22803092552148860608167413)
                    ·
                      refine ⟨2137789926763955682015695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22803092552148860608167413 2137789926763955682015695)
                      ·
                        rfl

theorem cell23_4163331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_4163331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163331 prefixEnd_4163331 := by exact prefixLift 4163331
  have htrace : WordTrace (prefixWord ++ tailWord_4163331) baseStart_4163331 baseEnd_4163331 := by
    simpa [prefixWord, tailWord_4163331, baseEnd_4163331] using wordTrace_append hprefix tailTrace_4163331
  have hstable : (prefixWord ++ tailWord_4163331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163331).length < 2 ^ (prefixWord ++ tailWord_4163331).sum := by decide
  have hdescent : baseEnd_4163331 < baseStart_4163331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163334 : List Nat := [6, 2, 2, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4163334 : Nat := 118140960795 + 4163334 * 2 ^ 59
def prefixEnd_4163334 : Nat := 4983230072969 + 3 ^ 40 * 4163334 * 2
def baseEnd_4163334 : Nat := 2137791467205919170278183

theorem tailTrace_4163334 : CollatzResearch.WordTrace tailWord_4163334 prefixEnd_4163334 2137791467205919170278183 := by
  unfold tailWord_4163334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4745289559342482302608033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101232843932639622455638037 4745289559342482302608033)
  ·
    refine ⟨3558967169506861726956025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4745289559342482302608033 3558967169506861726956025)
    ·
      refine ⟨2669225377130146295217019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3558967169506861726956025 2669225377130146295217019)
      ·
        refine ⟨4003838065695219442825529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669225377130146295217019 4003838065695219442825529)
        ·
          refine ⟨3002878549271414582119147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4003838065695219442825529 3002878549271414582119147)
          ·
            refine ⟨4504317823907121873178721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002878549271414582119147 4504317823907121873178721)
            ·
              refine ⟨3378238367930341404884041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4504317823907121873178721 3378238367930341404884041)
              ·
                refine ⟨2533678775947756053663031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3378238367930341404884041 2533678775947756053663031)
                ·
                  refine ⟨3800518163921634080494547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533678775947756053663031 3800518163921634080494547)
                  ·
                    refine ⟨5700777245882451120741821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3800518163921634080494547 5700777245882451120741821)
                    ·
                      refine ⟨2137791467205919170278183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5700777245882451120741821 2137791467205919170278183)
                      ·
                        rfl

theorem cell23_4163334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4163334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163334 prefixEnd_4163334 := by exact prefixLift 4163334
  have htrace : WordTrace (prefixWord ++ tailWord_4163334) baseStart_4163334 baseEnd_4163334 := by
    simpa [prefixWord, tailWord_4163334, baseEnd_4163334] using wordTrace_append hprefix tailTrace_4163334
  have hstable : (prefixWord ++ tailWord_4163334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163334).length < 2 ^ (prefixWord ++ tailWord_4163334).sum := by decide
  have hdescent : baseEnd_4163334 < baseStart_4163334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163362 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_4163362 : Nat := 118140960795 + 4163362 * 2 ^ 59
def prefixEnd_4163362 : Nat := 4983230072969 + 3 ^ 40 * 4163362 * 2
def baseEnd_4163362 : Nat := 2137805844664245060728053

theorem tailTrace_4163362 : CollatzResearch.WordTrace tailWord_4163362 prefixEnd_4163362 2137805844664245060728053 := by
  unfold tailWord_4163362
  simp only [CollatzResearch.WordTrace]
  refine ⟨37962571785714498616369085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101233524761905329643650893 37962571785714498616369085)
  ·
    refine ⟨14235964419642936981138407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37962571785714498616369085 14235964419642936981138407)
    ·
      refine ⟨21353946629464405471707611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14235964419642936981138407 21353946629464405471707611)
      ·
        refine ⟨32030919944196608207561417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21353946629464405471707611 32030919944196608207561417)
        ·
          refine ⟨24023189958147456155671063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32030919944196608207561417 24023189958147456155671063)
          ·
            refine ⟨36034784937221184233506595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24023189958147456155671063 36034784937221184233506595)
            ·
              refine ⟨54052177405831776350259893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36034784937221184233506595 54052177405831776350259893)
              ·
                refine ⟨5067391631796729032836865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54052177405831776350259893 5067391631796729032836865)
                ·
                  refine ⟨3800543723847546774627649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5067391631796729032836865 3800543723847546774627649)
                  ·
                    refine ⟨2850407792885660080970737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3800543723847546774627649 2850407792885660080970737)
                    ·
                      refine ⟨2137805844664245060728053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850407792885660080970737 2137805844664245060728053)
                      ·
                        rfl

theorem cell23_4163362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_4163362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163362 prefixEnd_4163362 := by exact prefixLift 4163362
  have htrace : WordTrace (prefixWord ++ tailWord_4163362) baseStart_4163362 baseEnd_4163362 := by
    simpa [prefixWord, tailWord_4163362, baseEnd_4163362] using wordTrace_append hprefix tailTrace_4163362
  have hstable : (prefixWord ++ tailWord_4163362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163362).length < 2 ^ (prefixWord ++ tailWord_4163362).sum := by decide
  have hdescent : baseEnd_4163362 < baseStart_4163362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163368 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 7]
def baseStart_4163368 : Nat := 118140960795 + 4163368 * 2 ^ 59
def prefixEnd_4163368 : Nat := 4983230072969 + 3 ^ 40 * 4163368 * 2
def baseEnd_4163368 : Nat := 237534325060908004139225

theorem tailTrace_4163368 : CollatzResearch.WordTrace tailWord_4163368 prefixEnd_4163368 237534325060908004139225 := by
  unfold tailWord_4163368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75925252990418128745097379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101233670653890838326796505 75925252990418128745097379)
  ·
    refine ⟨113887879485627193117646069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75925252990418128745097379 113887879485627193117646069)
    ·
      refine ⟨10676988701777549354779319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113887879485627193117646069 10676988701777549354779319)
      ·
        refine ⟨16015483052666324032168979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10676988701777549354779319 16015483052666324032168979)
        ·
          refine ⟨24023224578999486048253469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16015483052666324032168979 24023224578999486048253469)
          ·
            refine ⟨9008709217124807268095051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24023224578999486048253469 9008709217124807268095051)
            ·
              refine ⟨13513063825687210902142577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9008709217124807268095051 13513063825687210902142577)
              ·
                refine ⟨10134797869265408176606933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13513063825687210902142577 10134797869265408176606933)
                ·
                  refine ⟨237534325060908004139225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10134797869265408176606933 237534325060908004139225)
                  ·
                    rfl

theorem cell23_4163368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 7].length) (baseStart_4163368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163368 prefixEnd_4163368 := by exact prefixLift 4163368
  have htrace : WordTrace (prefixWord ++ tailWord_4163368) baseStart_4163368 baseEnd_4163368 := by
    simpa [prefixWord, tailWord_4163368, baseEnd_4163368] using wordTrace_append hprefix tailTrace_4163368
  have hstable : (prefixWord ++ tailWord_4163368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163368).length < 2 ^ (prefixWord ++ tailWord_4163368).sum := by decide
  have hdescent : baseEnd_4163368 < baseStart_4163368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163441 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 10]
def baseStart_4163441 : Nat := 118140960795 + 4163441 * 2 ^ 59
def prefixEnd_4163441 : Nat := 4983230072969 + 3 ^ 40 * 4163441 * 2
def baseEnd_4163441 : Nat := 237538489959550027960021

theorem tailTrace_4163441 : CollatzResearch.WordTrace tailWord_4163441 prefixEnd_4163441 237538489959550027960021 := by
  unfold tailWord_4163441
  simp only [CollatzResearch.WordTrace]
  refine ⟨151853168509571790957602177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101235445673047860638401451 151853168509571790957602177)
  ·
    refine ⟨113889876382178843218201633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151853168509571790957602177 113889876382178843218201633)
    ·
      refine ⟨85417407286634132413651225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113889876382178843218201633 85417407286634132413651225)
      ·
        refine ⟨64063055464975599310238419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85417407286634132413651225 64063055464975599310238419)
        ·
          refine ⟨96094583197463398965357629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64063055464975599310238419 96094583197463398965357629)
          ·
            refine ⟨36035468699048774612009111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96094583197463398965357629 36035468699048774612009111)
            ·
              refine ⟨54053203048573161918013667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36035468699048774612009111 54053203048573161918013667)
              ·
                refine ⟨81079804572859742877020501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54053203048573161918013667 81079804572859742877020501)
                ·
                  refine ⟨237538489959550027960021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 81079804572859742877020501 237538489959550027960021)
                  ·
                    rfl

theorem cell23_4163441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 10].length) (baseStart_4163441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163441 prefixEnd_4163441 := by exact prefixLift 4163441
  have htrace : WordTrace (prefixWord ++ tailWord_4163441) baseStart_4163441 baseEnd_4163441 := by
    simpa [prefixWord, tailWord_4163441, baseEnd_4163441] using wordTrace_append hprefix tailTrace_4163441
  have hstable : (prefixWord ++ tailWord_4163441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163441).length < 2 ^ (prefixWord ++ tailWord_4163441).sum := by decide
  have hdescent : baseEnd_4163441 < baseStart_4163441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163535 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 2, 4]
def baseStart_4163535 : Nat := 118140960795 + 4163535 * 2 ^ 59
def prefixEnd_4163535 : Nat := 4983230072969 + 3 ^ 40 * 4163535 * 2
def baseEnd_4163535 : Nat := 712631558939157627954919

theorem tailTrace_4163535 : CollatzResearch.WordTrace tailWord_4163535 prefixEnd_4163535 712631558939157627954919 := by
  unfold tailWord_4163535
  simp only [CollatzResearch.WordTrace]
  refine ⟨151856596971231245011524059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101237731314154163341016039 151856596971231245011524059)
  ·
    refine ⟨227784895456846867517286089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151856596971231245011524059 227784895456846867517286089)
    ·
      refine ⟨170838671592635150637964567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227784895456846867517286089 170838671592635150637964567)
      ·
        refine ⟨256258007388952725956946851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170838671592635150637964567 256258007388952725956946851)
        ·
          refine ⟨384387011083429088935420277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256258007388952725956946851 384387011083429088935420277)
          ·
            refine ⟨36036282289071477087695651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384387011083429088935420277 36036282289071477087695651)
            ·
              refine ⟨54054423433607215631543477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36036282289071477087695651 54054423433607215631543477)
              ·
                refine ⟨5067602196900676465457201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54054423433607215631543477 5067602196900676465457201)
                ·
                  refine ⟨3800701647675507349092901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5067602196900676465457201 3800701647675507349092901)
                  ·
                    refine ⟨712631558939157627954919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800701647675507349092901 712631558939157627954919)
                    ·
                      rfl

theorem cell23_4163535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 4].length) (baseStart_4163535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163535 prefixEnd_4163535 := by exact prefixLift 4163535
  have htrace : WordTrace (prefixWord ++ tailWord_4163535) baseStart_4163535 baseEnd_4163535 := by
    simpa [prefixWord, tailWord_4163535, baseEnd_4163535] using wordTrace_append hprefix tailTrace_4163535
  have hstable : (prefixWord ++ tailWord_4163535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163535).length < 2 ^ (prefixWord ++ tailWord_4163535).sum := by decide
  have hdescent : baseEnd_4163535 < baseStart_4163535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163546 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2]
def baseStart_4163546 : Nat := 118140960795 + 4163546 * 2 ^ 59
def prefixEnd_4163546 : Nat := 4983230072969 + 3 ^ 40 * 4163546 * 2
def baseEnd_4163546 : Nat := 2137900325104672340827207

theorem tailTrace_4163546 : CollatzResearch.WordTrace tailWord_4163546 prefixEnd_4163546 2137900325104672340827207 := by
  unfold tailWord_4163546
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964249543547848472543623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101237998782794262593449661 37964249543547848472543623)
  ·
    refine ⟨56946374315321772708815435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37964249543547848472543623 56946374315321772708815435)
    ·
      refine ⟨85419561472982659063223153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56946374315321772708815435 85419561472982659063223153)
      ·
        refine ⟨64064671104736994297417365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85419561472982659063223153 64064671104736994297417365)
        ·
          refine ⟨3003031458034546607691439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64064671104736994297417365 3003031458034546607691439)
          ·
            refine ⟨4504547187051819911537159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003031458034546607691439 4504547187051819911537159)
            ·
              refine ⟨6756820780577729867305739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504547187051819911537159 6756820780577729867305739)
              ·
                refine ⟨10135231170866594800958609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6756820780577729867305739 10135231170866594800958609)
                ·
                  refine ⟨7601423378149946100718957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10135231170866594800958609 7601423378149946100718957)
                  ·
                    refine ⟨2850533766806229787769609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7601423378149946100718957 2850533766806229787769609)
                    ·
                      refine ⟨2137900325104672340827207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850533766806229787769609 2137900325104672340827207)
                      ·
                        rfl

theorem cell23_4163546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_4163546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163546 prefixEnd_4163546 := by exact prefixLift 4163546
  have htrace : WordTrace (prefixWord ++ tailWord_4163546) baseStart_4163546 baseEnd_4163546 := by
    simpa [prefixWord, tailWord_4163546, baseEnd_4163546] using wordTrace_append hprefix tailTrace_4163546
  have hstable : (prefixWord ++ tailWord_4163546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163546).length < 2 ^ (prefixWord ++ tailWord_4163546).sum := by decide
  have hdescent : baseEnd_4163546 < baseStart_4163546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163555 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4163555 : Nat := 118140960795 + 4163555 * 2 ^ 59
def prefixEnd_4163555 : Nat := 4983230072969 + 3 ^ 40 * 4163555 * 2
def baseEnd_4163555 : Nat := 2137904946430562805614665

theorem tailTrace_4163555 : CollatzResearch.WordTrace tailWord_4163555 prefixEnd_4163555 2137904946430562805614665 := by
  unfold tailWord_4163555
  simp only [CollatzResearch.WordTrace]
  refine ⟨151857326431158788427252119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101238217620772525618168079 151857326431158788427252119)
  ·
    refine ⟨227785989646738182640878179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151857326431158788427252119 227785989646738182640878179)
    ·
      refine ⟨341678984470107273961317269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227785989646738182640878179 341678984470107273961317269)
      ·
        refine ⟨16016202397036278466936747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 341678984470107273961317269 16016202397036278466936747)
        ·
          refine ⟨24024303595554417700405121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16016202397036278466936747 24024303595554417700405121)
          ·
            refine ⟨18018227696665813275303841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24024303595554417700405121 18018227696665813275303841)
            ·
              refine ⟨13513670772499359956477881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18018227696665813275303841 13513670772499359956477881)
              ·
                refine ⟨10135253079374519967358411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13513670772499359956477881 10135253079374519967358411)
                ·
                  refine ⟨15202879619061779951037617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10135253079374519967358411 15202879619061779951037617)
                  ·
                    refine ⟨11402159714296334963278213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15202879619061779951037617 11402159714296334963278213)
                    ·
                      refine ⟨2137904946430562805614665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11402159714296334963278213 2137904946430562805614665)
                      ·
                        rfl

theorem cell23_4163555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4163555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163555 prefixEnd_4163555 := by exact prefixLift 4163555
  have htrace : WordTrace (prefixWord ++ tailWord_4163555) baseStart_4163555 baseEnd_4163555 := by
    simpa [prefixWord, tailWord_4163555, baseEnd_4163555] using wordTrace_append hprefix tailTrace_4163555
  have hstable : (prefixWord ++ tailWord_4163555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163555).length < 2 ^ (prefixWord ++ tailWord_4163555).sum := by decide
  have hdescent : baseEnd_4163555 < baseStart_4163555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163562 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_4163562 : Nat := 118140960795 + 4163562 * 2 ^ 59
def prefixEnd_4163562 : Nat := 4983230072969 + 3 ^ 40 * 4163562 * 2
def baseEnd_4163562 : Nat := 2137908540795144278227133

theorem tailTrace_4163562 : CollatzResearch.WordTrace tailWord_4163562 prefixEnd_4163562 2137908540795144278227133 := by
  unfold tailWord_4163562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964395435533357155689235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101238387828088952415171293 37964395435533357155689235)
  ·
    refine ⟨56946593153300035733533853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37964395435533357155689235 56946593153300035733533853)
    ·
      refine ⟨21354972432487513400075195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56946593153300035733533853 21354972432487513400075195)
      ·
        refine ⟨32032458648731270100112793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21354972432487513400075195 32032458648731270100112793)
        ·
          refine ⟨24024343986548452575084595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32032458648731270100112793 24024343986548452575084595)
          ·
            refine ⟨36036515979822678862626893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24024343986548452575084595 36036515979822678862626893)
            ·
              refine ⟨13513693492433504573485085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36036515979822678862626893 13513693492433504573485085)
              ·
                refine ⟨5067635059662564215056907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13513693492433504573485085 5067635059662564215056907)
                ·
                  refine ⟨7601452589493846322585361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067635059662564215056907 7601452589493846322585361)
                  ·
                    refine ⟨5701089442120384741939021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7601452589493846322585361 5701089442120384741939021)
                    ·
                      refine ⟨2137908540795144278227133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5701089442120384741939021 2137908540795144278227133)
                      ·
                        rfl

theorem cell23_4163562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_4163562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163562 prefixEnd_4163562 := by exact prefixLift 4163562
  have htrace : WordTrace (prefixWord ++ tailWord_4163562) baseStart_4163562 baseEnd_4163562 := by
    simpa [prefixWord, tailWord_4163562, baseEnd_4163562] using wordTrace_append hprefix tailTrace_4163562
  have hstable : (prefixWord ++ tailWord_4163562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163562).length < 2 ^ (prefixWord ++ tailWord_4163562).sum := by decide
  have hdescent : baseEnd_4163562 < baseStart_4163562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163569 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 2, 4]
def baseStart_4163569 : Nat := 118140960795 + 4163569 * 2 ^ 59
def prefixEnd_4163569 : Nat := 4983230072969 + 3 ^ 40 * 4163569 * 2
def baseEnd_4163569 : Nat := 712637378386575250279867

theorem tailTrace_4163569 : CollatzResearch.WordTrace tailWord_4163569 prefixEnd_4163569 712637378386575250279867 := by
  unfold tailWord_4163569
  simp only [CollatzResearch.WordTrace]
  refine ⟨151857837053108068818261761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101238558035405379212174507 151857837053108068818261761)
  ·
    refine ⟨113893377789831051613696321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151857837053108068818261761 113893377789831051613696321)
    ·
      refine ⟨85420033342373288710272241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113893377789831051613696321 85420033342373288710272241)
      ·
        refine ⟨64065025006779966532704181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85420033342373288710272241 64065025006779966532704181)
        ·
          refine ⟨6006096094385621862441017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64065025006779966532704181 6006096094385621862441017)
          ·
            refine ⟨4504572070789216396830763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6006096094385621862441017 4504572070789216396830763)
            ·
              refine ⟨6756858106183824595246145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504572070789216396830763 6756858106183824595246145)
              ·
                refine ⟨5067643579637868446434609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6756858106183824595246145 5067643579637868446434609)
                ·
                  refine ⟨3800732684728401334825957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5067643579637868446434609 3800732684728401334825957)
                  ·
                    refine ⟨712637378386575250279867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800732684728401334825957 712637378386575250279867)
                    ·
                      rfl

theorem cell23_4163569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_4163569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163569 prefixEnd_4163569 := by exact prefixLift 4163569
  have htrace : WordTrace (prefixWord ++ tailWord_4163569) baseStart_4163569 baseEnd_4163569 := by
    simpa [prefixWord, tailWord_4163569, baseEnd_4163569] using wordTrace_append hprefix tailTrace_4163569
  have hstable : (prefixWord ++ tailWord_4163569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163569).length < 2 ^ (prefixWord ++ tailWord_4163569).sum := by decide
  have hdescent : baseEnd_4163569 < baseStart_4163569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163628 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_4163628 : Nat := 118140960795 + 4163628 * 2 ^ 59
def prefixEnd_4163628 : Nat := 4983230072969 + 3 ^ 40 * 4163628 * 2
def baseEnd_4163628 : Nat := 2137942430518341020001829

theorem tailTrace_4163628 : CollatzResearch.WordTrace tailWord_4163628 prefixEnd_4163628 2137942430518341020001829 := by
  unfold tailWord_4163628
  simp only [CollatzResearch.WordTrace]
  refine ⟨75929994479947160947329769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101239992639929547929773025 75929994479947160947329769)
  ·
    refine ⟨56947495859960370710497327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75929994479947160947329769 56947495859960370710497327)
    ·
      refine ⟨85421243789940556065745991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56947495859960370710497327 85421243789940556065745991)
      ·
        refine ⟨128131865684910834098618987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85421243789940556065745991 128131865684910834098618987)
        ·
          refine ⟨192197798527366251147928481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128131865684910834098618987 192197798527366251147928481)
          ·
            refine ⟨144148348895524688360946361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192197798527366251147928481 144148348895524688360946361)
            ·
              refine ⟨108111261671643516270709771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144148348895524688360946361 108111261671643516270709771)
              ·
                refine ⟨162166892507465274406064657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108111261671643516270709771 162166892507465274406064657)
                ·
                  refine ⟨121625169380598955804548493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162166892507465274406064657 121625169380598955804548493)
                  ·
                    refine ⟨45609438517724608426705685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121625169380598955804548493 45609438517724608426705685)
                    ·
                      refine ⟨2137942430518341020001829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45609438517724608426705685 2137942430518341020001829)
                      ·
                        rfl

theorem cell23_4163628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_4163628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163628 prefixEnd_4163628 := by exact prefixLift 4163628
  have htrace : WordTrace (prefixWord ++ tailWord_4163628) baseStart_4163628 baseEnd_4163628 := by
    simpa [prefixWord, tailWord_4163628, baseEnd_4163628] using wordTrace_append hprefix tailTrace_4163628
  have hstable : (prefixWord ++ tailWord_4163628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163628).length < 2 ^ (prefixWord ++ tailWord_4163628).sum := by decide
  have hdescent : baseEnd_4163628 < baseStart_4163628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163645 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_4163645 : Nat := 118140960795 + 4163645 * 2 ^ 59
def prefixEnd_4163645 : Nat := 4983230072969 + 3 ^ 40 * 4163645 * 2
def baseEnd_4163645 : Nat := 2137951159689467453489251

theorem tailTrace_4163645 : CollatzResearch.WordTrace tailWord_4163645 prefixEnd_4163645 2137951159689467453489251 := by
  unfold tailWord_4163645
  simp only [CollatzResearch.WordTrace]
  refine ⟨151860609000832733798028389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101240406000555155865352259 151860609000832733798028389)
  ·
    refine ⟨28473864187656137587130323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151860609000832733798028389 28473864187656137587130323)
    ·
      refine ⟨42710796281484206380695485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28473864187656137587130323 42710796281484206380695485)
      ·
        refine ⟨16016548605556577392760807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42710796281484206380695485 16016548605556577392760807)
        ·
          refine ⟨24024822908334866089141211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16016548605556577392760807 24024822908334866089141211)
          ·
            refine ⟨36037234362502299133711817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24024822908334866089141211 36037234362502299133711817)
            ·
              refine ⟨27027925771876724350283863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36037234362502299133711817 27027925771876724350283863)
              ·
                refine ⟨40541888657815086525425795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27027925771876724350283863 40541888657815086525425795)
                ·
                  refine ⟨60812832986722629788138693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40541888657815086525425795 60812832986722629788138693)
                  ·
                    refine ⟨11402406185010493085276005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60812832986722629788138693 11402406185010493085276005)
                    ·
                      refine ⟨2137951159689467453489251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11402406185010493085276005 2137951159689467453489251)
                      ·
                        rfl

theorem cell23_4163645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_4163645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163645 prefixEnd_4163645 := by exact prefixLift 4163645
  have htrace : WordTrace (prefixWord ++ tailWord_4163645) baseStart_4163645 baseEnd_4163645 := by
    simpa [prefixWord, tailWord_4163645, baseEnd_4163645] using wordTrace_append hprefix tailTrace_4163645
  have hstable : (prefixWord ++ tailWord_4163645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163645).length < 2 ^ (prefixWord ++ tailWord_4163645).sum := by decide
  have hdescent : baseEnd_4163645 < baseStart_4163645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163665 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_4163665 : Nat := 118140960795 + 4163665 * 2 ^ 59
def prefixEnd_4163665 : Nat := 4983230072969 + 3 ^ 40 * 4163665 * 2
def baseEnd_4163665 : Nat := 2137961429302557375239159

theorem tailTrace_4163665 : CollatzResearch.WordTrace tailWord_4163665 prefixEnd_4163665 2137961429302557375239159 := by
  unfold tailWord_4163665
  simp only [CollatzResearch.WordTrace]
  refine ⟨151861338460760277213756449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101240892307173518142504299 151861338460760277213756449)
  ·
    refine ⟨113896003845570207910317337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151861338460760277213756449 113896003845570207910317337)
    ·
      refine ⟨85422002884177655932738003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113896003845570207910317337 85422002884177655932738003)
      ·
        refine ⟨128133004326266483899107005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85422002884177655932738003 128133004326266483899107005)
        ·
          refine ⟨48049876622349931462165127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128133004326266483899107005 48049876622349931462165127)
          ·
            refine ⟨72074814933524897193247691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48049876622349931462165127 72074814933524897193247691)
            ·
              refine ⟨108112222400287345789871537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72074814933524897193247691 108112222400287345789871537)
              ·
                refine ⟨81084166800215509342403653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108112222400287345789871537 81084166800215509342403653)
                ·
                  refine ⟨15203281275040408001700685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81084166800215509342403653 15203281275040408001700685)
                  ·
                    refine ⟨5701230478140153000637757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15203281275040408001700685 5701230478140153000637757)
                    ·
                      refine ⟨2137961429302557375239159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5701230478140153000637757 2137961429302557375239159)
                      ·
                        rfl

theorem cell23_4163665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_4163665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163665 prefixEnd_4163665 := by exact prefixLift 4163665
  have htrace : WordTrace (prefixWord ++ tailWord_4163665) baseStart_4163665 baseEnd_4163665 := by
    simpa [prefixWord, tailWord_4163665, baseEnd_4163665] using wordTrace_append hprefix tailTrace_4163665
  have hstable : (prefixWord ++ tailWord_4163665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163665).length < 2 ^ (prefixWord ++ tailWord_4163665).sum := by decide
  have hdescent : baseEnd_4163665 < baseStart_4163665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163670 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_4163670 : Nat := 118140960795 + 4163670 * 2 ^ 59
def prefixEnd_4163670 : Nat := 4983230072969 + 3 ^ 40 * 4163670 * 2
def baseEnd_4163670 : Nat := 2137963996705829855676637

theorem tailTrace_4163670 : CollatzResearch.WordTrace tailWord_4163670 prefixEnd_4163670 2137963996705829855676637 := by
  unfold tailWord_4163670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9491345051608885191730529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101241013883828108711792309 9491345051608885191730529)
  ·
    refine ⟨7118508788706663893797897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9491345051608885191730529 7118508788706663893797897)
    ·
      refine ⟨5338881591529997920348423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7118508788706663893797897 5338881591529997920348423)
      ·
        refine ⟨8008322387294996880522635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5338881591529997920348423 8008322387294996880522635)
        ·
          refine ⟨12012483580942495320783953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8008322387294996880522635 12012483580942495320783953)
          ·
            refine ⟨9009362685706871490587965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12012483580942495320783953 9009362685706871490587965)
            ·
              refine ⟨3378511007140076808970487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9009362685706871490587965 3378511007140076808970487)
              ·
                refine ⟨5067766510710115213455731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378511007140076808970487 5067766510710115213455731)
                ·
                  refine ⟨7601649766065172820183597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067766510710115213455731 7601649766065172820183597)
                  ·
                    refine ⟨2850618662274439807568849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7601649766065172820183597 2850618662274439807568849)
                    ·
                      refine ⟨2137963996705829855676637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850618662274439807568849 2137963996705829855676637)
                      ·
                        rfl

theorem cell23_4163670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_4163670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163670 prefixEnd_4163670 := by exact prefixLift 4163670
  have htrace : WordTrace (prefixWord ++ tailWord_4163670) baseStart_4163670 baseEnd_4163670 := by
    simpa [prefixWord, tailWord_4163670, baseEnd_4163670] using wordTrace_append hprefix tailTrace_4163670
  have hstable : (prefixWord ++ tailWord_4163670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163670).length < 2 ^ (prefixWord ++ tailWord_4163670).sum := by decide
  have hdescent : baseEnd_4163670 < baseStart_4163670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163692 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 2, 5, 2]
def baseStart_4163692 : Nat := 118140960795 + 4163692 * 2 ^ 59
def prefixEnd_4163692 : Nat := 4983230072969 + 3 ^ 40 * 4163692 * 2
def baseEnd_4163692 : Nat := 2137975293280228769601535

theorem tailTrace_4163692 : CollatzResearch.WordTrace tailWord_4163692 prefixEnd_4163692 2137975293280228769601535 := by
  unfold tailWord_4163692
  simp only [CollatzResearch.WordTrace]
  refine ⟨75931161615831230412494665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101241548821108307216659553 75931161615831230412494665)
  ·
    refine ⟨56948371211873422809370999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75931161615831230412494665 56948371211873422809370999)
    ·
      refine ⟨85422556817810134214056499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56948371211873422809370999 85422556817810134214056499)
      ·
        refine ⟨128133835226715201321084749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85422556817810134214056499 128133835226715201321084749)
        ·
          refine ⟨48050188210018200495406781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128133835226715201321084749 48050188210018200495406781)
          ·
            refine ⟨18018820578756825185777543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48050188210018200495406781 18018820578756825185777543)
            ·
              refine ⟨27028230868135237778666315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18018820578756825185777543 27028230868135237778666315)
              ·
                refine ⟨40542346302202856667999473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27028230868135237778666315 40542346302202856667999473)
                ·
                  refine ⟨30406759726652142500999605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40542346302202856667999473 30406759726652142500999605)
                  ·
                    refine ⟨2850633724373638359468713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30406759726652142500999605 2850633724373638359468713)
                    ·
                      refine ⟨2137975293280228769601535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850633724373638359468713 2137975293280228769601535)
                      ·
                        rfl

theorem cell23_4163692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_4163692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163692 prefixEnd_4163692 := by exact prefixLift 4163692
  have htrace : WordTrace (prefixWord ++ tailWord_4163692) baseStart_4163692 baseEnd_4163692 := by
    simpa [prefixWord, tailWord_4163692, baseEnd_4163692] using wordTrace_append hprefix tailTrace_4163692
  have hstable : (prefixWord ++ tailWord_4163692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163692).length < 2 ^ (prefixWord ++ tailWord_4163692).sum := by decide
  have hdescent : baseEnd_4163692 < baseStart_4163692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163695 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_4163695 : Nat := 118140960795 + 4163695 * 2 ^ 59
def prefixEnd_4163695 : Nat := 4983230072969 + 3 ^ 40 * 4163695 * 2
def baseEnd_4163695 : Nat := 2137976833722192257864021

theorem tailTrace_4163695 : CollatzResearch.WordTrace tailWord_4163695 prefixEnd_4163695 2137976833722192257864021 := by
  unfold tailWord_4163695
  simp only [CollatzResearch.WordTrace]
  refine ⟨151862432650651592337348539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101241621767101061558232359 151862432650651592337348539)
  ·
    refine ⟨227793648975977388506022809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151862432650651592337348539 227793648975977388506022809)
    ·
      refine ⟨170845236731983041379517107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227793648975977388506022809 170845236731983041379517107)
      ·
        refine ⟨256267855097974562069275661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170845236731983041379517107 256267855097974562069275661)
        ·
          refine ⟨96100445661740460775978373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256267855097974562069275661 96100445661740460775978373)
          ·
            refine ⟨18018833561576336395495945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96100445661740460775978373 18018833561576336395495945)
            ·
              refine ⟨13514125171182252296621959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18018833561576336395495945 13514125171182252296621959)
              ·
                refine ⟨20271187756773378444932939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13514125171182252296621959 20271187756773378444932939)
                ·
                  refine ⟨30406781635160067667399409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20271187756773378444932939 30406781635160067667399409)
                  ·
                    refine ⟨22805086226370050750549557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30406781635160067667399409 22805086226370050750549557)
                    ·
                      refine ⟨2137976833722192257864021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22805086226370050750549557 2137976833722192257864021)
                      ·
                        rfl

theorem cell23_4163695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_4163695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163695 prefixEnd_4163695 := by exact prefixLift 4163695
  have htrace : WordTrace (prefixWord ++ tailWord_4163695) baseStart_4163695 baseEnd_4163695 := by
    simpa [prefixWord, tailWord_4163695, baseEnd_4163695] using wordTrace_append hprefix tailTrace_4163695
  have hstable : (prefixWord ++ tailWord_4163695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163695).length < 2 ^ (prefixWord ++ tailWord_4163695).sum := by decide
  have hdescent : baseEnd_4163695 < baseStart_4163695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163722 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4163722 : Nat := 118140960795 + 4163722 * 2 ^ 59
def prefixEnd_4163722 : Nat := 4983230072969 + 3 ^ 40 * 4163722 * 2
def baseEnd_4163722 : Nat := 2137990697699863652226397

theorem tailTrace_4163722 : CollatzResearch.WordTrace tailWord_4163722 prefixEnd_4163722 2137990697699863652226397 := by
  unfold tailWord_4163722
  simp only [CollatzResearch.WordTrace]
  refine ⟨37965854355388443987145355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101242278281035850632387613 37965854355388443987145355)
  ·
    refine ⟨56948781533082665980718033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37965854355388443987145355 56948781533082665980718033)
    ·
      refine ⟨42711586149811999485538525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56948781533082665980718033 42711586149811999485538525)
      ·
        refine ⟨16016844806179499807076947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42711586149811999485538525 16016844806179499807076947)
        ·
          refine ⟨24025267209269249710615421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16016844806179499807076947 24025267209269249710615421)
          ·
            refine ⟨9009475203475968641480783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24025267209269249710615421 9009475203475968641480783)
            ·
              refine ⟨13514212805213952962221175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9009475203475968641480783 13514212805213952962221175)
              ·
                refine ⟨20271319207820929443331763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13514212805213952962221175 20271319207820929443331763)
                ·
                  refine ⟨30406978811731394164997645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20271319207820929443331763 30406978811731394164997645)
                  ·
                    refine ⟨11402617054399272811874117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30406978811731394164997645 11402617054399272811874117)
                    ·
                      refine ⟨2137990697699863652226397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11402617054399272811874117 2137990697699863652226397)
                      ·
                        rfl

theorem cell23_4163722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4163722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163722 prefixEnd_4163722 := by exact prefixLift 4163722
  have htrace : WordTrace (prefixWord ++ tailWord_4163722) baseStart_4163722 baseEnd_4163722 := by
    simpa [prefixWord, tailWord_4163722, baseEnd_4163722] using wordTrace_append hprefix tailTrace_4163722
  have hstable : (prefixWord ++ tailWord_4163722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163722).length < 2 ^ (prefixWord ++ tailWord_4163722).sum := by decide
  have hdescent : baseEnd_4163722 < baseStart_4163722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163749 : List Nat := [1, 3, 1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_4163749 : Nat := 118140960795 + 4163749 * 2 ^ 59
def prefixEnd_4163749 : Nat := 4983230072969 + 3 ^ 40 * 4163749 * 2
def baseEnd_4163749 : Nat := 712668187225845015529591

theorem tailTrace_4163749 : CollatzResearch.WordTrace tailWord_4163749 prefixEnd_4163749 712668187225845015529591 := by
  unfold tailWord_4163749
  simp only [CollatzResearch.WordTrace]
  refine ⟨151864402192455959559814301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101242934794970639706542867 151864402192455959559814301)
  ·
    refine ⟨56949150822170984834930363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151864402192455959559814301 56949150822170984834930363)
    ·
      refine ⟨85423726233256477252395545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56949150822170984834930363 85423726233256477252395545)
      ·
        refine ⟨64067794674942357939296659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85423726233256477252395545 64067794674942357939296659)
        ·
          refine ⟨96101692012413536908944989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64067794674942357939296659 96101692012413536908944989)
          ·
            refine ⟨36038134504655076340854371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96101692012413536908944989 36038134504655076340854371)
            ·
              refine ⟨54057201756982614511281557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36038134504655076340854371 54057201756982614511281557)
              ·
                refine ⟨2533931332358560055216323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54057201756982614511281557 2533931332358560055216323)
                ·
                  refine ⟨3800896998537840082824485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2533931332358560055216323 3800896998537840082824485)
                  ·
                    refine ⟨712668187225845015529591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3800896998537840082824485 712668187225845015529591)
                    ·
                      rfl

theorem cell23_4163749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_4163749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163749 prefixEnd_4163749 := by exact prefixLift 4163749
  have htrace : WordTrace (prefixWord ++ tailWord_4163749) baseStart_4163749 baseEnd_4163749 := by
    simpa [prefixWord, tailWord_4163749, baseEnd_4163749] using wordTrace_append hprefix tailTrace_4163749
  have hstable : (prefixWord ++ tailWord_4163749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163749).length < 2 ^ (prefixWord ++ tailWord_4163749).sum := by decide
  have hdescent : baseEnd_4163749 < baseStart_4163749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163812 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_4163812 : Nat := 118140960795 + 4163812 * 2 ^ 59
def prefixEnd_4163812 : Nat := 4983230072969 + 3 ^ 40 * 4163812 * 2
def baseEnd_4163812 : Nat := 2138036910958768300100983

theorem tailTrace_4163812 : CollatzResearch.WordTrace tailWord_4163812 prefixEnd_4163812 2138036910958768300100983 := by
  unfold tailWord_4163812
  simp only [CollatzResearch.WordTrace]
  refine ⟨75933349995613860659678845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101244466660818480879571793 75933349995613860659678845)
  ·
    refine ⟨28475006248355197747379567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75933349995613860659678845 28475006248355197747379567)
    ·
      refine ⟨42712509372532796621069351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28475006248355197747379567 42712509372532796621069351)
      ·
        refine ⟨64068764058799194931604027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42712509372532796621069351 64068764058799194931604027)
        ·
          refine ⟨96103146088198792397406041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64068764058799194931604027 96103146088198792397406041)
          ·
            refine ⟨72077359566149094298054531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96103146088198792397406041 72077359566149094298054531)
            ·
              refine ⟨108116039349223641447081797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72077359566149094298054531 108116039349223641447081797)
              ·
                refine ⟨20271757377979432771327837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108116039349223641447081797 20271757377979432771327837)
                ·
                  refine ⟨7601909016742287289247939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20271757377979432771327837 7601909016742287289247939)
                  ·
                    refine ⟨11402863525113430933871909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7601909016742287289247939 11402863525113430933871909)
                    ·
                      refine ⟨2138036910958768300100983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11402863525113430933871909 2138036910958768300100983)
                      ·
                        rfl

theorem cell23_4163812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_4163812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163812 prefixEnd_4163812 := by exact prefixLift 4163812
  have htrace : WordTrace (prefixWord ++ tailWord_4163812) baseStart_4163812 baseEnd_4163812 := by
    simpa [prefixWord, tailWord_4163812, baseEnd_4163812] using wordTrace_append hprefix tailTrace_4163812
  have hstable : (prefixWord ++ tailWord_4163812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163812).length < 2 ^ (prefixWord ++ tailWord_4163812).sum := by decide
  have hdescent : baseEnd_4163812 < baseStart_4163812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163822 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_4163822 : Nat := 118140960795 + 4163822 * 2 ^ 59
def prefixEnd_4163822 : Nat := 4983230072969 + 3 ^ 40 * 4163822 * 2
def baseEnd_4163822 : Nat := 712680681921771086991979

theorem tailTrace_4163822 : CollatzResearch.WordTrace tailWord_4163822 prefixEnd_4163822 712680681921771086991979 := by
  unfold tailWord_4163822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18983383090148936628402715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101244709814127662018147813 18983383090148936628402715)
  ·
    refine ⟨28475074635223404942604073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18983383090148936628402715 28475074635223404942604073)
    ·
      refine ⟨21356305976417553706953055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28475074635223404942604073 21356305976417553706953055)
      ·
        refine ⟨32034458964626330560429583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21356305976417553706953055 32034458964626330560429583)
        ·
          refine ⟨48051688446939495840644375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32034458964626330560429583 48051688446939495840644375)
          ·
            refine ⟨72077532670409243760966563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48051688446939495840644375 72077532670409243760966563)
            ·
              refine ⟨108116299005613865641449845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72077532670409243760966563 108116299005613865641449845)
              ·
                refine ⟨10135903031776299903885923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108116299005613865641449845 10135903031776299903885923)
                ·
                  refine ⟨15203854547664449855828885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10135903031776299903885923 15203854547664449855828885)
                  ·
                    refine ⟨712680681921771086991979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15203854547664449855828885 712680681921771086991979)
                    ·
                      rfl

theorem cell23_4163822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_4163822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163822 prefixEnd_4163822 := by exact prefixLift 4163822
  have htrace : WordTrace (prefixWord ++ tailWord_4163822) baseStart_4163822 baseEnd_4163822 := by
    simpa [prefixWord, tailWord_4163822, baseEnd_4163822] using wordTrace_append hprefix tailTrace_4163822
  have hstable : (prefixWord ++ tailWord_4163822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163822).length < 2 ^ (prefixWord ++ tailWord_4163822).sum := by decide
  have hdescent : baseEnd_4163822 < baseStart_4163822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163826 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_4163826 : Nat := 118140960795 + 4163826 * 2 ^ 59
def prefixEnd_4163826 : Nat := 4983230072969 + 3 ^ 40 * 4163826 * 2
def baseEnd_4163826 : Nat := 712681366562643748441973

theorem tailTrace_4163826 : CollatzResearch.WordTrace tailWord_4163826 prefixEnd_4163826 712681366562643748441973 := by
  unfold tailWord_4163826
  simp only [CollatzResearch.WordTrace]
  refine ⟨37966802653294250427591833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101244807075451334473578221 37966802653294250427591833)
  ·
    refine ⟨28475101989970687820693875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37966802653294250427591833 28475101989970687820693875)
    ·
      refine ⟨42712652984956031731040813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28475101989970687820693875 42712652984956031731040813)
      ·
        refine ⟨16017244869358511899140305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42712652984956031731040813 16017244869358511899140305)
        ·
          refine ⟨12012933652018883924355229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16017244869358511899140305 12012933652018883924355229)
          ·
            refine ⟨4504850119507081471633211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12012933652018883924355229 4504850119507081471633211)
            ·
              refine ⟨6757275179260622207449817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504850119507081471633211 6757275179260622207449817)
              ·
                refine ⟨5067956384445466655587363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757275179260622207449817 5067956384445466655587363)
                ·
                  refine ⟨7601934576668199983381045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5067956384445466655587363 7601934576668199983381045)
                  ·
                    refine ⟨712681366562643748441973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7601934576668199983381045 712681366562643748441973)
                    ·
                      rfl

theorem cell23_4163826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_4163826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163826 prefixEnd_4163826 := by exact prefixLift 4163826
  have htrace : WordTrace (prefixWord ++ tailWord_4163826) baseStart_4163826 baseEnd_4163826 := by
    simpa [prefixWord, tailWord_4163826, baseEnd_4163826] using wordTrace_append hprefix tailTrace_4163826
  have hstable : (prefixWord ++ tailWord_4163826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163826).length < 2 ^ (prefixWord ++ tailWord_4163826).sum := by decide
  have hdescent : baseEnd_4163826 < baseStart_4163826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163849 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 5]
def baseStart_4163849 : Nat := 118140960795 + 4163849 * 2 ^ 59
def prefixEnd_4163849 : Nat := 4983230072969 + 3 ^ 40 * 4163849 * 2
def baseEnd_4163849 : Nat := 2138055909742984655338313

theorem tailTrace_4163849 : CollatzResearch.WordTrace tailWord_4163849 prefixEnd_4163849 2138055909742984655338313 := by
  unfold tailWord_4163849
  simp only [CollatzResearch.WordTrace]
  refine ⟨151868049492093676638454601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101245366328062451092303067 151868049492093676638454601)
  ·
    refine ⟨113901037119070257478840951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151868049492093676638454601 113901037119070257478840951)
    ·
      refine ⟨170851555678605386218261427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113901037119070257478840951 170851555678605386218261427)
      ·
        refine ⟨256277333517908079327392141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170851555678605386218261427 256277333517908079327392141)
        ·
          refine ⟨96104000069215529747772053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256277333517908079327392141 96104000069215529747772053)
          ·
            refine ⟨4504875003244477956926815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96104000069215529747772053 4504875003244477956926815)
            ·
              refine ⟨6757312504866716935390223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4504875003244477956926815 6757312504866716935390223)
              ·
                refine ⟨10135968757300075403085335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757312504866716935390223 10135968757300075403085335)
                ·
                  refine ⟨15203953135950113104628003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10135968757300075403085335 15203953135950113104628003)
                  ·
                    refine ⟨22805929703925169656942005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15203953135950113104628003 22805929703925169656942005)
                    ·
                      refine ⟨2138055909742984655338313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22805929703925169656942005 2138055909742984655338313)
                      ·
                        rfl

theorem cell23_4163849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 5].length) (baseStart_4163849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163849 prefixEnd_4163849 := by exact prefixLift 4163849
  have htrace : WordTrace (prefixWord ++ tailWord_4163849) baseStart_4163849 baseEnd_4163849 := by
    simpa [prefixWord, tailWord_4163849, baseEnd_4163849] using wordTrace_append hprefix tailTrace_4163849
  have hstable : (prefixWord ++ tailWord_4163849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163849).length < 2 ^ (prefixWord ++ tailWord_4163849).sum := by decide
  have hdescent : baseEnd_4163849 < baseStart_4163849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163912 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 2, 6]
def baseStart_4163912 : Nat := 118140960795 + 4163912 * 2 ^ 59
def prefixEnd_4163912 : Nat := 4983230072969 + 3 ^ 40 * 4163912 * 2
def baseEnd_4163912 : Nat := 712696086341405969616841

theorem tailTrace_4163912 : CollatzResearch.WordTrace tailWord_4163912 prefixEnd_4163912 712696086341405969616841 := by
  unfold tailWord_4163912
  simp only [CollatzResearch.WordTrace]
  refine ⟨75935173645432719198998995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101246898193910292265331993 75935173645432719198998995)
  ·
    refine ⟨113902760468149078798498493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75935173645432719198998995 113902760468149078798498493)
    ·
      refine ⟨42713535175555904549436935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113902760468149078798498493 42713535175555904549436935)
      ·
        refine ⟨64070302763333856824155403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42713535175555904549436935 64070302763333856824155403)
        ·
          refine ⟨96105454145000785236233105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64070302763333856824155403 96105454145000785236233105)
          ·
            refine ⟨72079090608750588927174829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96105454145000785236233105 72079090608750588927174829)
            ·
              refine ⟨27029658978281470847690561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72079090608750588927174829 27029658978281470847690561)
              ·
                refine ⟨20272244233711103135767921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27029658978281470847690561 20272244233711103135767921)
                ·
                  refine ⟨15204183175283327351825941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20272244233711103135767921 15204183175283327351825941)
                  ·
                    refine ⟨712696086341405969616841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15204183175283327351825941 712696086341405969616841)
                    ·
                      rfl

theorem cell23_4163912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_4163912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163912 prefixEnd_4163912 := by exact prefixLift 4163912
  have htrace : WordTrace (prefixWord ++ tailWord_4163912) baseStart_4163912 baseEnd_4163912 := by
    simpa [prefixWord, tailWord_4163912, baseEnd_4163912] using wordTrace_append hprefix tailTrace_4163912
  have hstable : (prefixWord ++ tailWord_4163912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163912).length < 2 ^ (prefixWord ++ tailWord_4163912).sum := by decide
  have hdescent : baseEnd_4163912 < baseStart_4163912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163934 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_4163934 : Nat := 118140960795 + 4163934 * 2 ^ 59
def prefixEnd_4163934 : Nat := 4983230072969 + 3 ^ 40 * 4163934 * 2
def baseEnd_4163934 : Nat := 2138099555598616822775423

theorem tailTrace_4163934 : CollatzResearch.WordTrace tailWord_4163934 prefixEnd_4163934 2138099555598616822775423 := by
  unfold tailWord_4163934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18983893712098217019412357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101247433131190490770199237 18983893712098217019412357)
  ·
    refine ⟨3559480071018415691139817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18983893712098217019412357 3559480071018415691139817)
    ·
      refine ⟨2669610053263811768354863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3559480071018415691139817 2669610053263811768354863)
      ·
        refine ⟨4004415079895717652532295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669610053263811768354863 4004415079895717652532295)
        ·
          refine ⟨6006622619843576478798443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004415079895717652532295 6006622619843576478798443)
          ·
            refine ⟨9009933929765364718197665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006622619843576478798443 9009933929765364718197665)
            ·
              refine ⟨6757450447324023538648249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9009933929765364718197665 6757450447324023538648249)
              ·
                refine ⟨5068087835493017653986187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757450447324023538648249 5068087835493017653986187)
                ·
                  refine ⟨7602131753239526480979281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068087835493017653986187 7602131753239526480979281)
                  ·
                    refine ⟨5701598814929644860734461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7602131753239526480979281 5701598814929644860734461)
                    ·
                      refine ⟨2138099555598616822775423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5701598814929644860734461 2138099555598616822775423)
                      ·
                        rfl

theorem cell23_4163934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_4163934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163934 prefixEnd_4163934 := by exact prefixLift 4163934
  have htrace : WordTrace (prefixWord ++ tailWord_4163934) baseStart_4163934 baseEnd_4163934 := by
    simpa [prefixWord, tailWord_4163934, baseEnd_4163934] using wordTrace_append hprefix tailTrace_4163934
  have hstable : (prefixWord ++ tailWord_4163934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163934).length < 2 ^ (prefixWord ++ tailWord_4163934).sum := by decide
  have hdescent : baseEnd_4163934 < baseStart_4163934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4163959 : List Nat := [1, 1, 3, 1, 1, 2, 2, 7, 5]
def baseStart_4163959 : Nat := 118140960795 + 4163959 * 2 ^ 59
def prefixEnd_4163959 : Nat := 4983230072969 + 3 ^ 40 * 4163959 * 2
def baseEnd_4163959 : Nat := 237568043623886580551423

theorem tailTrace_4163959 : CollatzResearch.WordTrace tailWord_4163959 prefixEnd_4163959 237568043623886580551423 := by
  unfold tailWord_4163959
  simp only [CollatzResearch.WordTrace]
  refine ⟨151872061521695165424958931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101248041014463443616639287 151872061521695165424958931)
  ·
    refine ⟨227808092282542748137438397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151872061521695165424958931 227808092282542748137438397)
    ·
      refine ⟨85428034605953530551539399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227808092282542748137438397 85428034605953530551539399)
      ·
        refine ⟨128142051908930295827309099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85428034605953530551539399 128142051908930295827309099)
        ·
          refine ⟨192213077863395443740963649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128142051908930295827309099 192213077863395443740963649)
          ·
            refine ⟨144159808397546582805722737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192213077863395443740963649 144159808397546582805722737)
            ·
              refine ⟨108119856298159937104292053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144159808397546582805722737 108119856298159937104292053)
              ·
                refine ⟨2534059131988123525881845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108119856298159937104292053 2534059131988123525881845)
                ·
                  refine ⟨237568043623886580551423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2534059131988123525881845 237568043623886580551423)
                  ·
                    rfl

theorem cell23_4163959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 5].length) (baseStart_4163959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4163959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4163959 prefixEnd_4163959 := by exact prefixLift 4163959
  have htrace : WordTrace (prefixWord ++ tailWord_4163959) baseStart_4163959 baseEnd_4163959 := by
    simpa [prefixWord, tailWord_4163959, baseEnd_4163959] using wordTrace_append hprefix tailTrace_4163959
  have hstable : (prefixWord ++ tailWord_4163959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4163959).length < 2 ^ (prefixWord ++ tailWord_4163959).sum := by decide
  have hdescent : baseEnd_4163959 < baseStart_4163959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4163959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164063 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 3]
def baseStart_4164063 : Nat := 118140960795 + 4164063 * 2 ^ 59
def prefixEnd_4164063 : Nat := 4983230072969 + 3 ^ 40 * 4164063 * 2
def baseEnd_4164063 : Nat := 2138165794603046818062329

theorem tailTrace_4164063 : CollatzResearch.WordTrace tailWord_4164063 prefixEnd_4164063 2138165794603046818062329 := by
  unfold tailWord_4164063
  simp only [CollatzResearch.WordTrace]
  refine ⟨151875854713318391186744843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101250569808878927457829895 151875854713318391186744843)
  ·
    refine ⟨227813782069977586780117265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151875854713318391186744843 227813782069977586780117265)
    ·
      refine ⟨170860336552483190085087949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227813782069977586780117265 170860336552483190085087949)
      ·
        refine ⟨64072626207181196281907981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170860336552483190085087949 64072626207181196281907981)
        ·
          refine ⟨24027234827692948605715493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64072626207181196281907981 24027234827692948605715493)
          ·
            refine ⟨4505106530192427863571655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24027234827692948605715493 4505106530192427863571655)
            ·
              refine ⟨6757659795288641795357483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505106530192427863571655 6757659795288641795357483)
              ·
                refine ⟨10136489692932962693036225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757659795288641795357483 10136489692932962693036225)
                ·
                  refine ⟨7602367269699722019777169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10136489692932962693036225 7602367269699722019777169)
                  ·
                    refine ⟨5701775452274791514832877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7602367269699722019777169 5701775452274791514832877)
                    ·
                      refine ⟨2138165794603046818062329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5701775452274791514832877 2138165794603046818062329)
                      ·
                        rfl

theorem cell23_4164063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_4164063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164063 prefixEnd_4164063 := by exact prefixLift 4164063
  have htrace : WordTrace (prefixWord ++ tailWord_4164063) baseStart_4164063 baseEnd_4164063 := by
    simpa [prefixWord, tailWord_4164063, baseEnd_4164063] using wordTrace_append hprefix tailTrace_4164063
  have hstable : (prefixWord ++ tailWord_4164063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164063).length < 2 ^ (prefixWord ++ tailWord_4164063).sum := by decide
  have hdescent : baseEnd_4164063 < baseStart_4164063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164076 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 3]
def baseStart_4164076 : Nat := 118140960795 + 4164076 * 2 ^ 59
def prefixEnd_4164076 : Nat := 4983230072969 + 3 ^ 40 * 4164076 * 2
def baseEnd_4164076 : Nat := 2138172469851555267199769

theorem tailTrace_4164076 : CollatzResearch.WordTrace tailWord_4164076 prefixEnd_4164076 2138172469851555267199769 := by
  unfold tailWord_4164076
  simp only [CollatzResearch.WordTrace]
  refine ⟨75938164431135647203484041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101250885908180862937978721 75938164431135647203484041)
  ·
    refine ⟨56953623323351735402613031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75938164431135647203484041 56953623323351735402613031)
    ·
      refine ⟨85430434985027603103919547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56953623323351735402613031 85430434985027603103919547)
      ·
        refine ⟨128145652477541404655879321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85430434985027603103919547 128145652477541404655879321)
        ·
          refine ⟨96109239358156053491909491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128145652477541404655879321 96109239358156053491909491)
          ·
            refine ⟨144163859037234080237864237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96109239358156053491909491 144163859037234080237864237)
            ·
              refine ⟨54061447138962780089199089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144163859037234080237864237 54061447138962780089199089)
              ·
                refine ⟨40546085354222085066899317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54061447138962780089199089 40546085354222085066899317)
                ·
                  refine ⟨3801195501958320475021811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40546085354222085066899317 3801195501958320475021811)
                  ·
                    refine ⟨5701793252937480712532717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3801195501958320475021811 5701793252937480712532717)
                    ·
                      refine ⟨2138172469851555267199769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5701793252937480712532717 2138172469851555267199769)
                      ·
                        rfl

theorem cell23_4164076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_4164076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164076 prefixEnd_4164076 := by exact prefixLift 4164076
  have htrace : WordTrace (prefixWord ++ tailWord_4164076) baseStart_4164076 baseEnd_4164076 := by
    simpa [prefixWord, tailWord_4164076, baseEnd_4164076] using wordTrace_append hprefix tailTrace_4164076
  have hstable : (prefixWord ++ tailWord_4164076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164076).length < 2 ^ (prefixWord ++ tailWord_4164076).sum := by decide
  have hdescent : baseEnd_4164076 < baseStart_4164076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164093 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_4164093 : Nat := 118140960795 + 4164093 * 2 ^ 59
def prefixEnd_4164093 : Nat := 4983230072969 + 3 ^ 40 * 4164093 * 2
def baseEnd_4164093 : Nat := 2138181199022681700687191

theorem tailTrace_4164093 : CollatzResearch.WordTrace tailWord_4164093 prefixEnd_4164093 2138181199022681700687191 := by
  unfold tailWord_4164093
  simp only [CollatzResearch.WordTrace]
  refine ⟨151876948903209706310336933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101251299268806470873557955 151876948903209706310336933)
  ·
    refine ⟨28476927919351819933188175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151876948903209706310336933 28476927919351819933188175)
    ·
      refine ⟨42715391879027729899782263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28476927919351819933188175 42715391879027729899782263)
      ·
        refine ⟨64073087818541594849673395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42715391879027729899782263 64073087818541594849673395)
        ·
          refine ⟨96109631727812392274510093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64073087818541594849673395 96109631727812392274510093)
          ·
            refine ⟨36041111897929647102941285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96109631727812392274510093 36041111897929647102941285)
            ·
              refine ⟨6757708480861808831801491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36041111897929647102941285 6757708480861808831801491)
              ·
                refine ⟨10136562721292713247702237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6757708480861808831801491 10136562721292713247702237)
                ·
                  refine ⟨3801211020484767467888339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10136562721292713247702237 3801211020484767467888339)
                  ·
                    refine ⟨5701816530727151201832509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3801211020484767467888339 5701816530727151201832509)
                    ·
                      refine ⟨2138181199022681700687191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5701816530727151201832509 2138181199022681700687191)
                      ·
                        rfl

theorem cell23_4164093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_4164093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164093 prefixEnd_4164093 := by exact prefixLift 4164093
  have htrace : WordTrace (prefixWord ++ tailWord_4164093) baseStart_4164093 baseEnd_4164093 := by
    simpa [prefixWord, tailWord_4164093, baseEnd_4164093] using wordTrace_append hprefix tailTrace_4164093
  have hstable : (prefixWord ++ tailWord_4164093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164093).length < 2 ^ (prefixWord ++ tailWord_4164093).sum := by decide
  have hdescent : baseEnd_4164093 < baseStart_4164093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164133 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 5, 2, 2]
def baseStart_4164133 : Nat := 118140960795 + 4164133 * 2 ^ 59
def prefixEnd_4164133 : Nat := 4983230072969 + 3 ^ 40 * 4164133 * 2
def baseEnd_4164133 : Nat := 2138201738248861544187007

theorem tailTrace_4164133 : CollatzResearch.WordTrace tailWord_4164133 prefixEnd_4164133 2138201738248861544187007 := by
  unfold tailWord_4164133
  simp only [CollatzResearch.WordTrace]
  refine ⟨151878407823064793141793053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101252271882043195427862035 151878407823064793141793053)
  ·
    refine ⟨56954402933649297428172395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151878407823064793141793053 56954402933649297428172395)
    ·
      refine ⟨85431604400473946142258593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56954402933649297428172395 85431604400473946142258593)
      ·
        refine ⟨64073703300355459606693945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85431604400473946142258593 64073703300355459606693945)
        ·
          refine ⟨48055277475266594705020459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64073703300355459606693945 48055277475266594705020459)
          ·
            refine ⟨72082916212899892057530689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48055277475266594705020459 72082916212899892057530689)
            ·
              refine ⟨54062187159674919043148017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72082916212899892057530689 54062187159674919043148017)
              ·
                refine ⟨40546640369756189282361013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54062187159674919043148017 40546640369756189282361013)
                ·
                  refine ⟨3801247534664642745221345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40546640369756189282361013 3801247534664642745221345)
                  ·
                    refine ⟨2850935650998482058916009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3801247534664642745221345 2850935650998482058916009)
                    ·
                      refine ⟨2138201738248861544187007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2850935650998482058916009 2138201738248861544187007)
                      ·
                        rfl

theorem cell23_4164133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_4164133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164133 prefixEnd_4164133 := by exact prefixLift 4164133
  have htrace : WordTrace (prefixWord ++ tailWord_4164133) baseStart_4164133 baseEnd_4164133 := by
    simpa [prefixWord, tailWord_4164133, baseEnd_4164133] using wordTrace_append hprefix tailTrace_4164133
  have hstable : (prefixWord ++ tailWord_4164133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164133).length < 2 ^ (prefixWord ++ tailWord_4164133).sum := by decide
  have hdescent : baseEnd_4164133 < baseStart_4164133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164156 : List Nat := [2, 2, 2, 2, 3, 2, 2, 8]
def baseStart_4164156 : Nat := 118140960795 + 4164156 * 2 ^ 59
def prefixEnd_4164156 : Nat := 4983230072969 + 3 ^ 40 * 4164156 * 2
def baseEnd_4164156 : Nat := 79193094381626479785163

theorem tailTrace_4164156 : CollatzResearch.WordTrace tailWord_4164156 prefixEnd_4164156 79193094381626479785163 := by
  unfold tailWord_4164156
  simp only [CollatzResearch.WordTrace]
  refine ⟨75939623350990734034940161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101252831134654312046586881 75939623350990734034940161)
  ·
    refine ⟨56954717513243050526205121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75939623350990734034940161 56954717513243050526205121)
    ·
      refine ⟨42716038134932287894653841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56954717513243050526205121 42716038134932287894653841)
      ·
        refine ⟨32037028601199215920990381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42716038134932287894653841 32037028601199215920990381)
        ·
          refine ⟨12013885725449705970371393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32037028601199215920990381 12013885725449705970371393)
          ·
            refine ⟨9010414294087279477778545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12013885725449705970371393 9010414294087279477778545)
            ·
              refine ⟨6757810720565459608333909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9010414294087279477778545 6757810720565459608333909)
              ·
                refine ⟨79193094381626479785163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6757810720565459608333909 79193094381626479785163)
                ·
                  rfl

theorem cell23_4164156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 8].length) (baseStart_4164156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164156 prefixEnd_4164156 := by exact prefixLift 4164156
  have htrace : WordTrace (prefixWord ++ tailWord_4164156) baseStart_4164156 baseEnd_4164156 := by
    simpa [prefixWord, tailWord_4164156, baseEnd_4164156] using wordTrace_append hprefix tailTrace_4164156
  have hstable : (prefixWord ++ tailWord_4164156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164156).length < 2 ^ (prefixWord ++ tailWord_4164156).sum := by decide
  have hdescent : baseEnd_4164156 < baseStart_4164156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164159 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_4164159 : Nat := 118140960795 + 4164159 * 2 ^ 59
def prefixEnd_4164159 : Nat := 4983230072969 + 3 ^ 40 * 4164159 * 2
def baseEnd_4164159 : Nat := 2138215088745878442461887

theorem tailTrace_4164159 : CollatzResearch.WordTrace tailWord_4164159 prefixEnd_4164159 2138215088745878442461887 := by
  unfold tailWord_4164159
  simp only [CollatzResearch.WordTrace]
  refine ⟨151879356120970599582239531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101252904080647066388159687 151879356120970599582239531)
  ·
    refine ⟨227819034181455899373359297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151879356120970599582239531 227819034181455899373359297)
    ·
      refine ⟨170864275636091924530019473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227819034181455899373359297 170864275636091924530019473)
      ·
        refine ⟨128148206727068943397514605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170864275636091924530019473 128148206727068943397514605)
        ·
          refine ⟨48055577522650853774067977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128148206727068943397514605 48055577522650853774067977)
          ·
            refine ⟨36041683141988140330550983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48055577522650853774067977 36041683141988140330550983)
            ·
              refine ⟨54062524712982210495826475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36041683141988140330550983 54062524712982210495826475)
              ·
                refine ⟨81093787069473315743739713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54062524712982210495826475 81093787069473315743739713)
                ·
                  refine ⟨60820340302104986807804785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81093787069473315743739713 60820340302104986807804785)
                  ·
                    refine ⟨45615255226578740105853589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60820340302104986807804785 45615255226578740105853589)
                    ·
                      refine ⟨2138215088745878442461887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45615255226578740105853589 2138215088745878442461887)
                      ·
                        rfl

theorem cell23_4164159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_4164159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164159 prefixEnd_4164159 := by exact prefixLift 4164159
  have htrace : WordTrace (prefixWord ++ tailWord_4164159) baseStart_4164159 baseEnd_4164159 := by
    simpa [prefixWord, tailWord_4164159, baseEnd_4164159] using wordTrace_append hprefix tailTrace_4164159
  have hstable : (prefixWord ++ tailWord_4164159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164159).length < 2 ^ (prefixWord ++ tailWord_4164159).sum := by decide
  have hdescent : baseEnd_4164159 < baseStart_4164159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164164 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4164164 : Nat := 118140960795 + 4164164 * 2 ^ 59
def prefixEnd_4164164 : Nat := 4983230072969 + 3 ^ 40 * 4164164 * 2
def baseEnd_4164164 : Nat := 712739218716383640966455

theorem tailTrace_4164164 : CollatzResearch.WordTrace tailWord_4164164 prefixEnd_4164164 712739218716383640966455 := by
  unfold tailWord_4164164
  simp only [CollatzResearch.WordTrace]
  refine ⟨75939769242976242718085773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101253025657301656957447697 75939769242976242718085773)
  ·
    refine ⟨28477413466116091019282165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75939769242976242718085773 28477413466116091019282165)
    ·
      refine ⟨2669757512448383533057703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28477413466116091019282165 2669757512448383533057703)
      ·
        refine ⟨4004636268672575299586555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2669757512448383533057703 4004636268672575299586555)
        ·
          refine ⟨6006954403008862949379833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004636268672575299586555 6006954403008862949379833)
          ·
            refine ⟨4505215802256647212034875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6006954403008862949379833 4505215802256647212034875)
            ·
              refine ⟨6757823703384970818052313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505215802256647212034875 6757823703384970818052313)
              ·
                refine ⟨5068367777538728113539235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757823703384970818052313 5068367777538728113539235)
                ·
                  refine ⟨7602551666308092170308853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068367777538728113539235 7602551666308092170308853)
                  ·
                    refine ⟨712739218716383640966455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7602551666308092170308853 712739218716383640966455)
                    ·
                      rfl

theorem cell23_4164164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4164164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164164 prefixEnd_4164164 := by exact prefixLift 4164164
  have htrace : WordTrace (prefixWord ++ tailWord_4164164) baseStart_4164164 baseEnd_4164164 := by
    simpa [prefixWord, tailWord_4164164, baseEnd_4164164] using wordTrace_append hprefix tailTrace_4164164
  have hstable : (prefixWord ++ tailWord_4164164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164164).length < 2 ^ (prefixWord ++ tailWord_4164164).sum := by decide
  have hdescent : baseEnd_4164164 < baseStart_4164164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164170 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_4164170 : Nat := 118140960795 + 4164170 * 2 ^ 59
def prefixEnd_4164170 : Nat := 4983230072969 + 3 ^ 40 * 4164170 * 2
def baseEnd_4164170 : Nat := 2138220737033077899424337

theorem tailTrace_4164170 : CollatzResearch.WordTrace tailWord_4164170 prefixEnd_4164170 2138220737033077899424337 := by
  unfold tailWord_4164170
  simp only [CollatzResearch.WordTrace]
  refine ⟨37969939330982687115222491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101253171549287165640593309 37969939330982687115222491)
  ·
    refine ⟨56954908996474030672833737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37969939330982687115222491 56954908996474030672833737)
    ·
      refine ⟨42716181747355523004625303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56954908996474030672833737 42716181747355523004625303)
      ·
        refine ⟨64074272621033284506937955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42716181747355523004625303 64074272621033284506937955)
        ·
          refine ⟨96111408931549926760406933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64074272621033284506937955 96111408931549926760406933)
          ·
            refine ⟨4505222293666402816894075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96111408931549926760406933 4505222293666402816894075)
            ·
              refine ⟨6757833440499604225341113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4505222293666402816894075 6757833440499604225341113)
              ·
                refine ⟨5068375080374703169005835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757833440499604225341113 5068375080374703169005835)
                ·
                  refine ⟨7602562620562054753508753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068375080374703169005835 7602562620562054753508753)
                  ·
                    refine ⟨5701921965421541065131565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7602562620562054753508753 5701921965421541065131565)
                    ·
                      refine ⟨2138220737033077899424337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5701921965421541065131565 2138220737033077899424337)
                      ·
                        rfl

theorem cell23_4164170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_4164170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164170 prefixEnd_4164170 := by exact prefixLift 4164170
  have htrace : WordTrace (prefixWord ++ tailWord_4164170) baseStart_4164170 baseEnd_4164170 := by
    simpa [prefixWord, tailWord_4164170, baseEnd_4164170] using wordTrace_append hprefix tailTrace_4164170
  have hstable : (prefixWord ++ tailWord_4164170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164170).length < 2 ^ (prefixWord ++ tailWord_4164170).sum := by decide
  have hdescent : baseEnd_4164170 < baseStart_4164170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164190 : List Nat := [4, 4, 1, 2, 1, 11]
def baseStart_4164190 : Nat := 118140960795 + 4164190 * 2 ^ 59
def prefixEnd_4164190 : Nat := 4983230072969 + 3 ^ 40 * 4164190 * 2
def baseEnd_4164190 : Nat := 8799304554099456054215

theorem tailTrace_4164190 : CollatzResearch.WordTrace tailWord_4164190 prefixEnd_4164190 8799304554099456054215 := by
  unfold tailWord_4164190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18985060847982286484577253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101253657855905527917745349 18985060847982286484577253)
  ·
    refine ⟨3559698908996678715858235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18985060847982286484577253 3559698908996678715858235)
    ·
      refine ⟨5339548363495018073787353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3559698908996678715858235 5339548363495018073787353)
      ·
        refine ⟨4004661272621263555340515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5339548363495018073787353 4004661272621263555340515)
        ·
          refine ⟨6006991908931895333010773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004661272621263555340515 6006991908931895333010773)
          ·
            refine ⟨8799304554099456054215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6006991908931895333010773 8799304554099456054215)
            ·
              rfl

theorem cell23_4164190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 11].length) (baseStart_4164190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164190 prefixEnd_4164190 := by exact prefixLift 4164190
  have htrace : WordTrace (prefixWord ++ tailWord_4164190) baseStart_4164190 baseEnd_4164190 := by
    simpa [prefixWord, tailWord_4164190, baseEnd_4164190] using wordTrace_append hprefix tailTrace_4164190
  have hstable : (prefixWord ++ tailWord_4164190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164190).length < 2 ^ (prefixWord ++ tailWord_4164190).sum := by decide
  have hdescent : baseEnd_4164190 < baseStart_4164190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164244 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_4164244 : Nat := 118140960795 + 4164244 * 2 ^ 59
def prefixEnd_4164244 : Nat := 4983230072969 + 3 ^ 40 * 4164244 * 2
def baseEnd_4164244 : Nat := 2138258734601510609898997

theorem tailTrace_4164244 : CollatzResearch.WordTrace tailWord_4164244 prefixEnd_4164244 2138258734601510609898997 := by
  unfold tailWord_4164244
  simp only [CollatzResearch.WordTrace]
  refine ⟨75941228162831329549541893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101254970883775106066055857 75941228162831329549541893)
  ·
    refine ⟨14238980280530874290539105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75941228162831329549541893 14238980280530874290539105)
    ·
      refine ⟨10679235210398155717904329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14238980280530874290539105 10679235210398155717904329)
      ·
        refine ⟨8009426407798616788428247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10679235210398155717904329 8009426407798616788428247)
        ·
          refine ⟨12014139611697925182642371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8009426407798616788428247 12014139611697925182642371)
          ·
            refine ⟨18021209417546887773963557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12014139611697925182642371 18021209417546887773963557)
            ·
              refine ⟨3378976765790041457618167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18021209417546887773963557 3378976765790041457618167)
              ·
                refine ⟨5068465148685062186427251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3378976765790041457618167 5068465148685062186427251)
                ·
                  refine ⟨7602697723027593279640877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068465148685062186427251 7602697723027593279640877)
                  ·
                    refine ⟨2851011646135347479865329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7602697723027593279640877 2851011646135347479865329)
                    ·
                      refine ⟨2138258734601510609898997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851011646135347479865329 2138258734601510609898997)
                      ·
                        rfl

theorem cell23_4164244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_4164244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164244 prefixEnd_4164244 := by exact prefixLift 4164244
  have htrace : WordTrace (prefixWord ++ tailWord_4164244) baseStart_4164244 baseEnd_4164244 := by
    simpa [prefixWord, tailWord_4164244, baseEnd_4164244] using wordTrace_append hprefix tailTrace_4164244
  have hstable : (prefixWord ++ tailWord_4164244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164244).length < 2 ^ (prefixWord ++ tailWord_4164244).sum := by decide
  have hdescent : baseEnd_4164244 < baseStart_4164244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164257 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_4164257 : Nat := 118140960795 + 4164257 * 2 ^ 59
def prefixEnd_4164257 : Nat := 4983230072969 + 3 ^ 40 * 4164257 * 2
def baseEnd_4164257 : Nat := 2138265409850019059036437

theorem tailTrace_4164257 : CollatzResearch.WordTrace tailWord_4164257 prefixEnd_4164257 2138265409850019059036437 := by
  unfold tailWord_4164257
  simp only [CollatzResearch.WordTrace]
  refine ⟨151882930474615562319307025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101255286983077041546204683 151882930474615562319307025)
  ·
    refine ⟨113912197855961671739480269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151882930474615562319307025 113912197855961671739480269)
    ·
      refine ⟨42717074195985626902305101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113912197855961671739480269 42717074195985626902305101)
      ·
        refine ⟨16018902823494610088364413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42717074195985626902305101 16018902823494610088364413)
        ·
          refine ⟨6007088558810478783136655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16018902823494610088364413 6007088558810478783136655)
          ·
            refine ⟨9010632838215718174704983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007088558810478783136655 9010632838215718174704983)
            ·
              refine ⟨13515949257323577262057475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9010632838215718174704983 13515949257323577262057475)
              ·
                refine ⟨20273923885985365893086213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13515949257323577262057475 20273923885985365893086213)
                ·
                  refine ⟨3801360728622256104953665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20273923885985365893086213 3801360728622256104953665)
                  ·
                    refine ⟨2851020546466692078715249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3801360728622256104953665 2851020546466692078715249)
                    ·
                      refine ⟨2138265409850019059036437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851020546466692078715249 2138265409850019059036437)
                      ·
                        rfl

theorem cell23_4164257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_4164257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164257 prefixEnd_4164257 := by exact prefixLift 4164257
  have htrace : WordTrace (prefixWord ++ tailWord_4164257) baseStart_4164257 baseEnd_4164257 := by
    simpa [prefixWord, tailWord_4164257, baseEnd_4164257] using wordTrace_append hprefix tailTrace_4164257
  have hstable : (prefixWord ++ tailWord_4164257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164257).length < 2 ^ (prefixWord ++ tailWord_4164257).sum := by decide
  have hdescent : baseEnd_4164257 < baseStart_4164257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164270 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4164270 : Nat := 118140960795 + 4164270 * 2 ^ 59
def prefixEnd_4164270 : Nat := 4983230072969 + 3 ^ 40 * 4164270 * 2
def baseEnd_4164270 : Nat := 2138272085098527508173877

theorem tailTrace_4164270 : CollatzResearch.WordTrace tailWord_4164270 prefixEnd_4164270 2138272085098527508173877 := by
  unfold tailWord_4164270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18985425577946058192441283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101255603082378977026353509 18985425577946058192441283)
  ·
    refine ⟨28478138366919087288661925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18985425577946058192441283 28478138366919087288661925)
    ·
      refine ⟨5339650943797328866624111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28478138366919087288661925 5339650943797328866624111)
      ·
        refine ⟨8009476415695993299936167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339650943797328866624111 8009476415695993299936167)
        ·
          refine ⟨12014214623543989949904251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8009476415695993299936167 12014214623543989949904251)
          ·
            refine ⟨18021321935315984924856377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12014214623543989949904251 18021321935315984924856377)
            ·
              refine ⟨13515991451486988693642283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18021321935315984924856377 13515991451486988693642283)
              ·
                refine ⟨20273987177230483040463425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13515991451486988693642283 20273987177230483040463425)
                ·
                  refine ⟨15205490382922862280347569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20273987177230483040463425 15205490382922862280347569)
                  ·
                    refine ⟨11404117787192146710260677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15205490382922862280347569 11404117787192146710260677)
                    ·
                      refine ⟨2138272085098527508173877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11404117787192146710260677 2138272085098527508173877)
                      ·
                        rfl

theorem cell23_4164270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4164270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164270 prefixEnd_4164270 := by exact prefixLift 4164270
  have htrace : WordTrace (prefixWord ++ tailWord_4164270) baseStart_4164270 baseEnd_4164270 := by
    simpa [prefixWord, tailWord_4164270, baseEnd_4164270] using wordTrace_append hprefix tailTrace_4164270
  have hstable : (prefixWord ++ tailWord_4164270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164270).length < 2 ^ (prefixWord ++ tailWord_4164270).sum := by decide
  have hdescent : baseEnd_4164270 < baseStart_4164270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164313 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_4164313 : Nat := 118140960795 + 4164313 * 2 ^ 59
def prefixEnd_4164313 : Nat := 4983230072969 + 3 ^ 40 * 4164313 * 2
def baseEnd_4164313 : Nat := 2138294164766670839936179

theorem tailTrace_4164313 : CollatzResearch.WordTrace tailWord_4164313 prefixEnd_4164313 2138294164766670839936179 := by
  unfold tailWord_4164313
  simp only [CollatzResearch.WordTrace]
  refine ⟨151884972962412683883345593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101256648641608455922230395 151884972962412683883345593)
  ·
    refine ⟨113913729721809512912509195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151884972962412683883345593 113913729721809512912509195)
    ·
      refine ⟨170870594582714269368763793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113913729721809512912509195 170870594582714269368763793)
      ·
        refine ⟨128152945937035702026572845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170870594582714269368763793 128152945937035702026572845)
        ·
          refine ⟨48057354726388388259964817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128152945937035702026572845 48057354726388388259964817)
          ·
            refine ⟨36043016044791291194973613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48057354726388388259964817 36043016044791291194973613)
            ·
              refine ⟨13516131016796734198115105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36043016044791291194973613 13516131016796734198115105)
              ·
                refine ⟨10137098262597550648586329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13516131016796734198115105 10137098262597550648586329)
                ·
                  refine ⟨7602823696948162986439747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10137098262597550648586329 7602823696948162986439747)
                  ·
                    refine ⟨11404235545422244479659621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7602823696948162986439747 11404235545422244479659621)
                    ·
                      refine ⟨2138294164766670839936179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11404235545422244479659621 2138294164766670839936179)
                      ·
                        rfl

theorem cell23_4164313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_4164313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164313 prefixEnd_4164313 := by exact prefixLift 4164313
  have htrace : WordTrace (prefixWord ++ tailWord_4164313) baseStart_4164313 baseEnd_4164313 := by
    simpa [prefixWord, tailWord_4164313, baseEnd_4164313] using wordTrace_append hprefix tailTrace_4164313
  have hstable : (prefixWord ++ tailWord_4164313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164313).length < 2 ^ (prefixWord ++ tailWord_4164313).sum := by decide
  have hdescent : baseEnd_4164313 < baseStart_4164313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164383 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 3, 5]
def baseStart_4164383 : Nat := 118140960795 + 4164383 * 2 ^ 59
def prefixEnd_4164383 : Nat := 4983230072969 + 3 ^ 40 * 4164383 * 2
def baseEnd_4164383 : Nat := 712776702804161855353619

theorem tailTrace_4164383 : CollatzResearch.WordTrace tailWord_4164383 prefixEnd_4164383 712776702804161855353619 := by
  unfold tailWord_4164383
  simp only [CollatzResearch.WordTrace]
  refine ⟨151887526072159085838393803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101258350714772723892262535 151887526072159085838393803)
  ·
    refine ⟨227831289108238628757590705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151887526072159085838393803 227831289108238628757590705)
    ·
      refine ⟨170873466831178971568193029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227831289108238628757590705 170873466831178971568193029)
      ·
        refine ⟨32038775030846057169036193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170873466831178971568193029 32038775030846057169036193)
        ·
          refine ⟨24029081273134542876777145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32038775030846057169036193 24029081273134542876777145)
          ·
            refine ⟨18021810954850907157582859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24029081273134542876777145 18021810954850907157582859)
            ·
              refine ⟨27032716432276360736374289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18021810954850907157582859 27032716432276360736374289)
              ·
                refine ⟨20274537324207270552280717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27032716432276360736374289 20274537324207270552280717)
                ·
                  refine ⟨7602951496577726457105269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20274537324207270552280717 7602951496577726457105269)
                  ·
                    refine ⟨712776702804161855353619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7602951496577726457105269 712776702804161855353619)
                    ·
                      rfl

theorem cell23_4164383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_4164383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164383 prefixEnd_4164383 := by exact prefixLift 4164383
  have htrace : WordTrace (prefixWord ++ tailWord_4164383) baseStart_4164383 baseEnd_4164383 := by
    simpa [prefixWord, tailWord_4164383, baseEnd_4164383] using wordTrace_append hprefix tailTrace_4164383
  have hstable : (prefixWord ++ tailWord_4164383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164383).length < 2 ^ (prefixWord ++ tailWord_4164383).sum := by decide
  have hdescent : baseEnd_4164383 < baseStart_4164383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164423 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_4164423 : Nat := 118140960795 + 4164423 * 2 ^ 59
def prefixEnd_4164423 : Nat := 4983230072969 + 3 ^ 40 * 4164423 * 2
def baseEnd_4164423 : Nat := 2138350647638665409560673

theorem tailTrace_4164423 : CollatzResearch.WordTrace tailWord_4164423 prefixEnd_4164423 2138350647638665409560673 := by
  unfold tailWord_4164423
  simp only [CollatzResearch.WordTrace]
  refine ⟨151888984992014172669849923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101259323328009448446566615 151888984992014172669849923)
  ·
    refine ⟨227833477488021259004774885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151888984992014172669849923 227833477488021259004774885)
    ·
      refine ⟨42718777029003986063395291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227833477488021259004774885 42718777029003986063395291)
      ·
        refine ⟨64078165543505979095092937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42718777029003986063395291 64078165543505979095092937)
        ·
          refine ⟨48058624157629484321319703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64078165543505979095092937 48058624157629484321319703)
          ·
            refine ⟨72087936236444226481979555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48058624157629484321319703 72087936236444226481979555)
            ·
              refine ⟨108131904354666339722969333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72087936236444226481979555 108131904354666339722969333)
              ·
                refine ⟨10137366033249969349028375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108131904354666339722969333 10137366033249969349028375)
                ·
                  refine ⟨15206049049874954023542563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10137366033249969349028375 15206049049874954023542563)
                  ·
                    refine ⟨22809073574812431035313845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15206049049874954023542563 22809073574812431035313845)
                    ·
                      refine ⟨2138350647638665409560673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22809073574812431035313845 2138350647638665409560673)
                      ·
                        rfl

theorem cell23_4164423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_4164423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164423 prefixEnd_4164423 := by exact prefixLift 4164423
  have htrace : WordTrace (prefixWord ++ tailWord_4164423) baseStart_4164423 baseEnd_4164423 := by
    simpa [prefixWord, tailWord_4164423, baseEnd_4164423] using wordTrace_append hprefix tailTrace_4164423
  have hstable : (prefixWord ++ tailWord_4164423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164423).length < 2 ^ (prefixWord ++ tailWord_4164423).sum := by decide
  have hdescent : baseEnd_4164423 < baseStart_4164423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164447 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 2, 4]
def baseStart_4164447 : Nat := 118140960795 + 4164447 * 2 ^ 59
def prefixEnd_4164447 : Nat := 4983230072969 + 3 ^ 40 * 4164447 * 2
def baseEnd_4164447 : Nat := 712787657058124438553521

theorem tailTrace_4164447 : CollatzResearch.WordTrace tailWord_4164447 prefixEnd_4164447 712787657058124438553521 := by
  unfold tailWord_4164447
  simp only [CollatzResearch.WordTrace]
  refine ⟨151889860343927224768723595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101259906895951483179149063 151889860343927224768723595)
  ·
    refine ⟨227834790515890837153085393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151889860343927224768723595 227834790515890837153085393)
    ·
      refine ⟨170876092886918127864814045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227834790515890837153085393 170876092886918127864814045)
      ·
        refine ⟨64078534832594297949305267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170876092886918127864814045 64078534832594297949305267)
        ·
          refine ⟨96117802248891446923957901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64078534832594297949305267 96117802248891446923957901)
          ·
            refine ⟨36044175843334292596484213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96117802248891446923957901 36044175843334292596484213)
            ·
              refine ⟨3379141485312589930920395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36044175843334292596484213 3379141485312589930920395)
              ·
                refine ⟨5068712227968884896380593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379141485312589930920395 5068712227968884896380593)
                ·
                  refine ⟨3801534170976663672285445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5068712227968884896380593 3801534170976663672285445)
                  ·
                    refine ⟨712787657058124438553521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3801534170976663672285445 712787657058124438553521)
                    ·
                      rfl

theorem cell23_4164447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 4].length) (baseStart_4164447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164447 prefixEnd_4164447 := by exact prefixLift 4164447
  have htrace : WordTrace (prefixWord ++ tailWord_4164447) baseStart_4164447 baseEnd_4164447 := by
    simpa [prefixWord, tailWord_4164447, baseEnd_4164447] using wordTrace_append hprefix tailTrace_4164447
  have hstable : (prefixWord ++ tailWord_4164447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164447).length < 2 ^ (prefixWord ++ tailWord_4164447).sum := by decide
  have hdescent : baseEnd_4164447 < baseStart_4164447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164483 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 5]
def baseStart_4164483 : Nat := 118140960795 + 4164483 * 2 ^ 59
def prefixEnd_4164483 : Nat := 4983230072969 + 3 ^ 40 * 4164483 * 2
def baseEnd_4164483 : Nat := 2138381456477935174810397

theorem tailTrace_4164483 : CollatzResearch.WordTrace tailWord_4164483 prefixEnd_4164483 2138381456477935174810397 := by
  unfold tailWord_4164483
  simp only [CollatzResearch.WordTrace]
  refine ⟨151891173371796802917034103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101260782247864535278022735 151891173371796802917034103)
  ·
    refine ⟨227836760057695204375551155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151891173371796802917034103 227836760057695204375551155)
    ·
      refine ⟨341755140086542806563326733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227836760057695204375551155 341755140086542806563326733)
      ·
        refine ⟨128158177532453552461247525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341755140086542806563326733 128158177532453552461247525)
        ·
          refine ⟨24029658287335041086483911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128158177532453552461247525 24029658287335041086483911)
          ·
            refine ⟨36044487431002561629725867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24029658287335041086483911 36044487431002561629725867)
            ·
              refine ⟨54066731146503842444588801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36044487431002561629725867 54066731146503842444588801)
              ·
                refine ⟨40550048359877881833441601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54066731146503842444588801 40550048359877881833441601)
                ·
                  refine ⟨30412536269908411375081201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40550048359877881833441601 30412536269908411375081201)
                  ·
                    refine ⟨22809402202431308531310901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30412536269908411375081201 22809402202431308531310901)
                    ·
                      refine ⟨2138381456477935174810397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22809402202431308531310901 2138381456477935174810397)
                      ·
                        rfl

theorem cell23_4164483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_4164483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164483 prefixEnd_4164483 := by exact prefixLift 4164483
  have htrace : WordTrace (prefixWord ++ tailWord_4164483) baseStart_4164483 baseEnd_4164483 := by
    simpa [prefixWord, tailWord_4164483, baseEnd_4164483] using wordTrace_append hprefix tailTrace_4164483
  have hstable : (prefixWord ++ tailWord_4164483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164483).length < 2 ^ (prefixWord ++ tailWord_4164483).sum := by decide
  have hdescent : baseEnd_4164483 < baseStart_4164483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164487 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_4164487 : Nat := 118140960795 + 4164487 * 2 ^ 59
def prefixEnd_4164487 : Nat := 4983230072969 + 3 ^ 40 * 4164487 * 2
def baseEnd_4164487 : Nat := 2138383510400553159160379

theorem tailTrace_4164487 : CollatzResearch.WordTrace tailWord_4164487 prefixEnd_4164487 2138383510400553159160379 := by
  unfold tailWord_4164487
  simp only [CollatzResearch.WordTrace]
  refine ⟨151891319263782311600179715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101260879509188207733453143 151891319263782311600179715)
  ·
    refine ⟨227836978895673467400269573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151891319263782311600179715 227836978895673467400269573)
    ·
      refine ⟨42719433542938775137550545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227836978895673467400269573 42719433542938775137550545)
      ·
        refine ⟨32039575157204081353162909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42719433542938775137550545 32039575157204081353162909)
        ·
          refine ⟨12014840683951530507436091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32039575157204081353162909 12014840683951530507436091)
          ·
            refine ⟨18022261025927295761154137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12014840683951530507436091 18022261025927295761154137)
            ·
              refine ⟨13516695769445471820865603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18022261025927295761154137 13516695769445471820865603)
              ·
                refine ⟨20275043654168207731298405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13516695769445471820865603 20275043654168207731298405)
                ·
                  refine ⟨3801570685156538949618451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20275043654168207731298405 3801570685156538949618451)
                  ·
                    refine ⟨5702356027734808424427677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3801570685156538949618451 5702356027734808424427677)
                    ·
                      refine ⟨2138383510400553159160379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5702356027734808424427677 2138383510400553159160379)
                      ·
                        rfl

theorem cell23_4164487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_4164487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164487 prefixEnd_4164487 := by exact prefixLift 4164487
  have htrace : WordTrace (prefixWord ++ tailWord_4164487) baseStart_4164487 baseEnd_4164487 := by
    simpa [prefixWord, tailWord_4164487, baseEnd_4164487] using wordTrace_append hprefix tailTrace_4164487
  have hstable : (prefixWord ++ tailWord_4164487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164487).length < 2 ^ (prefixWord ++ tailWord_4164487).sum := by decide
  have hdescent : baseEnd_4164487 < baseStart_4164487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164488 : List Nat := [2, 1, 3, 3, 2, 2, 3, 2, 1, 2, 2]
def baseStart_4164488 : Nat := 118140960795 + 4164488 * 2 ^ 59
def prefixEnd_4164488 : Nat := 4983230072969 + 3 ^ 40 * 4164488 * 2
def baseEnd_4164488 : Nat := 2138384023881207655247875

theorem tailTrace_4164488 : CollatzResearch.WordTrace tailWord_4164488 prefixEnd_4164488 2138384023881207655247875 := by
  unfold tailWord_4164488
  simp only [CollatzResearch.WordTrace]
  refine ⟨75945677868389344385483059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101260903824519125847310745 75945677868389344385483059)
  ·
    refine ⟨113918516802584016578224589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75945677868389344385483059 113918516802584016578224589)
    ·
      refine ⟨42719443800969006216834221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113918516802584016578224589 42719443800969006216834221)
      ·
        refine ⟨16019791425363377331312833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42719443800969006216834221 16019791425363377331312833)
        ·
          refine ⟨12014843569022532998484625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16019791425363377331312833 12014843569022532998484625)
          ·
            refine ⟨9011132676766899748863469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12014843569022532998484625 9011132676766899748863469)
            ·
              refine ⟨3379174753787587405823801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9011132676766899748863469 3379174753787587405823801)
              ·
                refine ⟨2534381065340690554367851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379174753787587405823801 2534381065340690554367851)
                ·
                  refine ⟨3801571598011035831551777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534381065340690554367851 3801571598011035831551777)
                  ·
                    refine ⟨2851178698508276873663833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3801571598011035831551777 2851178698508276873663833)
                    ·
                      refine ⟨2138384023881207655247875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851178698508276873663833 2138384023881207655247875)
                      ·
                        rfl

theorem cell23_4164488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_4164488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164488 prefixEnd_4164488 := by exact prefixLift 4164488
  have htrace : WordTrace (prefixWord ++ tailWord_4164488) baseStart_4164488 baseEnd_4164488 := by
    simpa [prefixWord, tailWord_4164488, baseEnd_4164488] using wordTrace_append hprefix tailTrace_4164488
  have hstable : (prefixWord ++ tailWord_4164488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164488).length < 2 ^ (prefixWord ++ tailWord_4164488).sum := by decide
  have hdescent : baseEnd_4164488 < baseStart_4164488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164498 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_4164498 : Nat := 118140960795 + 4164498 * 2 ^ 59
def prefixEnd_4164498 : Nat := 4983230072969 + 3 ^ 40 * 4164498 * 2
def baseEnd_4164498 : Nat := 712796386229250872040943

theorem tailTrace_4164498 : CollatzResearch.WordTrace tailWord_4164498 prefixEnd_4164498 712796386229250872040943 := by
  unfold tailWord_4164498
  simp only [CollatzResearch.WordTrace]
  refine ⟨37972930116685615119707537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101261146977828306985886765 37972930116685615119707537)
  ·
    refine ⟨28479697587514211339780653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37972930116685615119707537 28479697587514211339780653)
    ·
      refine ⟨10679886595317829252417745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28479697587514211339780653 10679886595317829252417745)
      ·
        refine ⟨8009914946488371939313309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10679886595317829252417745 8009914946488371939313309)
        ·
          refine ⟨3003718104933139477242491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8009914946488371939313309 3003718104933139477242491)
          ·
            refine ⟨4505577157399709215863737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003718104933139477242491 4505577157399709215863737)
            ·
              refine ⟨3379182868049781911897803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4505577157399709215863737 3379182868049781911897803)
              ·
                refine ⟨5068774302074672867846705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379182868049781911897803 5068774302074672867846705)
                ·
                  refine ⟨3801580726556004650885029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5068774302074672867846705 3801580726556004650885029)
                  ·
                    refine ⟨712796386229250872040943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3801580726556004650885029 712796386229250872040943)
                    ·
                      rfl

theorem cell23_4164498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_4164498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164498 prefixEnd_4164498 := by exact prefixLift 4164498
  have htrace : WordTrace (prefixWord ++ tailWord_4164498) baseStart_4164498 baseEnd_4164498 := by
    simpa [prefixWord, tailWord_4164498, baseEnd_4164498] using wordTrace_append hprefix tailTrace_4164498
  have hstable : (prefixWord ++ tailWord_4164498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164498).length < 2 ^ (prefixWord ++ tailWord_4164498).sum := by decide
  have hdescent : baseEnd_4164498 < baseStart_4164498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164503 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 1, 8]
def baseStart_4164503 : Nat := 118140960795 + 4164503 * 2 ^ 59
def prefixEnd_4164503 : Nat := 4983230072969 + 3 ^ 40 * 4164503 * 2
def baseEnd_4164503 : Nat := 712797242030341698853435

theorem tailTrace_4164503 : CollatzResearch.WordTrace tailWord_4164503 prefixEnd_4164503 712797242030341698853435 := by
  unfold tailWord_4164503
  simp only [CollatzResearch.WordTrace]
  refine ⟨151891902831724346332762163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101261268554482897555174775 151891902831724346332762163)
  ·
    refine ⟨227837854247586519499143245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151891902831724346332762163 227837854247586519499143245)
    ·
      refine ⟨85439195342844944812178717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227837854247586519499143245 85439195342844944812178717)
      ·
        refine ⟨32039698253566854304567019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85439195342844944812178717 32039698253566854304567019)
        ·
          refine ⟨48059547380350281456850529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32039698253566854304567019 48059547380350281456850529)
          ·
            refine ⟨36044660535262711092637897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48059547380350281456850529 36044660535262711092637897)
            ·
              refine ⟨27033495401447033319478423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36044660535262711092637897 27033495401447033319478423)
              ·
                refine ⟨40550243102170549979217635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27033495401447033319478423 40550243102170549979217635)
                ·
                  refine ⟨60825364653255824968826453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40550243102170549979217635 60825364653255824968826453)
                  ·
                    refine ⟨712797242030341698853435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60825364653255824968826453 712797242030341698853435)
                    ·
                      rfl

theorem cell23_4164503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_4164503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164503 prefixEnd_4164503 := by exact prefixLift 4164503
  have htrace : WordTrace (prefixWord ++ tailWord_4164503) baseStart_4164503 baseEnd_4164503 := by
    simpa [prefixWord, tailWord_4164503, baseEnd_4164503] using wordTrace_append hprefix tailTrace_4164503
  have hstable : (prefixWord ++ tailWord_4164503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164503).length < 2 ^ (prefixWord ++ tailWord_4164503).sum := by decide
  have hdescent : baseEnd_4164503 < baseStart_4164503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164514 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_4164514 : Nat := 118140960795 + 4164514 * 2 ^ 59
def prefixEnd_4164514 : Nat := 4983230072969 + 3 ^ 40 * 4164514 * 2
def baseEnd_4164514 : Nat := 2138397374378224553522755

theorem tailTrace_4164514 : CollatzResearch.WordTrace tailWord_4164514 prefixEnd_4164514 2138397374378224553522755 := by
  unfold tailWord_4164514
  simp only [CollatzResearch.WordTrace]
  refine ⟨37973076008671123802853149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101261536023122996807608397 37973076008671123802853149)
  ·
    refine ⟨14239903503251671426069931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37973076008671123802853149 14239903503251671426069931)
    ·
      refine ⟨21359855254877507139104897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14239903503251671426069931 21359855254877507139104897)
      ·
        refine ⟨16019891441158130354328673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21359855254877507139104897 16019891441158130354328673)
        ·
          refine ⟨12014918580868597765746505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16019891441158130354328673 12014918580868597765746505)
          ·
            refine ⟨9011188935651448324309879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12014918580868597765746505 9011188935651448324309879)
            ·
              refine ⟨13516783403477172486464819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9011188935651448324309879 13516783403477172486464819)
              ·
                refine ⟨20275175105215758729697229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13516783403477172486464819 20275175105215758729697229)
                ·
                  refine ⟨7603190664455909523636461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20275175105215758729697229 7603190664455909523636461)
                  ·
                    refine ⟨2851196499170966071363673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7603190664455909523636461 2851196499170966071363673)
                    ·
                      refine ⟨2138397374378224553522755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851196499170966071363673 2138397374378224553522755)
                      ·
                        rfl

theorem cell23_4164514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_4164514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164514 prefixEnd_4164514 := by exact prefixLift 4164514
  have htrace : WordTrace (prefixWord ++ tailWord_4164514) baseStart_4164514 baseEnd_4164514 := by
    simpa [prefixWord, tailWord_4164514, baseEnd_4164514] using wordTrace_append hprefix tailTrace_4164514
  have hstable : (prefixWord ++ tailWord_4164514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164514).length < 2 ^ (prefixWord ++ tailWord_4164514).sum := by decide
  have hdescent : baseEnd_4164514 < baseStart_4164514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164523 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 4]
def baseStart_4164523 : Nat := 118140960795 + 4164523 * 2 ^ 59
def prefixEnd_4164523 : Nat := 4983230072969 + 3 ^ 40 * 4164523 * 2
def baseEnd_4164523 : Nat := 2138401995704115018310213

theorem tailTrace_4164523 : CollatzResearch.WordTrace tailWord_4164523 prefixEnd_4164523 2138401995704115018310213 := by
  unfold tailWord_4164523
  simp only [CollatzResearch.WordTrace]
  refine ⟨151892632291651889748490223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101261754861101259832326815 151892632291651889748490223)
  ·
    refine ⟨227838948437477834622735335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151892632291651889748490223 227838948437477834622735335)
    ·
      refine ⟨341758422656216751934103003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227838948437477834622735335 341758422656216751934103003)
      ·
        refine ⟨512637633984325127901154505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341758422656216751934103003 512637633984325127901154505)
        ·
          refine ⟨384478225488243845925865879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512637633984325127901154505 384478225488243845925865879)
          ·
            refine ⟨576717338232365768888798819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384478225488243845925865879 576717338232365768888798819)
            ·
              refine ⟨865076007348548653333198229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576717338232365768888798819 865076007348548653333198229)
              ·
                refine ⟨40550437844463218124993667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 865076007348548653333198229 40550437844463218124993667)
                ·
                  refine ⟨60825656766694827187490501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40550437844463218124993667 60825656766694827187490501)
                  ·
                    refine ⟨11404810643755280097654469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60825656766694827187490501 11404810643755280097654469)
                    ·
                      refine ⟨2138401995704115018310213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11404810643755280097654469 2138401995704115018310213)
                      ·
                        rfl

theorem cell23_4164523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 4].length) (baseStart_4164523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164523 prefixEnd_4164523 := by exact prefixLift 4164523
  have htrace : WordTrace (prefixWord ++ tailWord_4164523) baseStart_4164523 baseEnd_4164523 := by
    simpa [prefixWord, tailWord_4164523, baseEnd_4164523] using wordTrace_append hprefix tailTrace_4164523
  have hstable : (prefixWord ++ tailWord_4164523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164523).length < 2 ^ (prefixWord ++ tailWord_4164523).sum := by decide
  have hdescent : baseEnd_4164523 < baseStart_4164523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164527 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 4, 2, 2]
def baseStart_4164527 : Nat := 118140960795 + 4164527 * 2 ^ 59
def prefixEnd_4164527 : Nat := 4983230072969 + 3 ^ 40 * 4164527 * 2
def baseEnd_4164527 : Nat := 2138404049626733002660195

theorem tailTrace_4164527 : CollatzResearch.WordTrace tailWord_4164527 prefixEnd_4164527 2138404049626733002660195 := by
  unfold tailWord_4164527
  simp only [CollatzResearch.WordTrace]
  refine ⟨151892778183637398431635835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101261852122424932287757223 151892778183637398431635835)
  ·
    refine ⟨227839167275456097647453753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151892778183637398431635835 227839167275456097647453753)
    ·
      refine ⟨170879375456592073235590315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227839167275456097647453753 170879375456592073235590315)
      ·
        refine ⟨256319063184888109853385473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170879375456592073235590315 256319063184888109853385473)
        ·
          refine ⟨192239297388666082390039105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256319063184888109853385473 192239297388666082390039105)
          ·
            refine ⟨144179473041499561792529329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192239297388666082390039105 144179473041499561792529329)
            ·
              refine ⟨108134604781124671344396997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144179473041499561792529329 108134604781124671344396997)
              ·
                refine ⟨20275238396460875877074437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108134604781124671344396997 20275238396460875877074437)
                ·
                  refine ⟨3801607199336414226951457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20275238396460875877074437 3801607199336414226951457)
                  ·
                    refine ⟨2851205399502310670213593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3801607199336414226951457 2851205399502310670213593)
                    ·
                      refine ⟨2138404049626733002660195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851205399502310670213593 2138404049626733002660195)
                      ·
                        rfl

theorem cell23_4164527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 2, 2].length) (baseStart_4164527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164527 prefixEnd_4164527 := by exact prefixLift 4164527
  have htrace : WordTrace (prefixWord ++ tailWord_4164527) baseStart_4164527 baseEnd_4164527 := by
    simpa [prefixWord, tailWord_4164527, baseEnd_4164527] using wordTrace_append hprefix tailTrace_4164527
  have hstable : (prefixWord ++ tailWord_4164527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164527).length < 2 ^ (prefixWord ++ tailWord_4164527).sum := by decide
  have hdescent : baseEnd_4164527 < baseStart_4164527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164544 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 2, 2, 2]
def baseStart_4164544 : Nat := 118140960795 + 4164544 * 2 ^ 59
def prefixEnd_4164544 : Nat := 4983230072969 + 3 ^ 40 * 4164544 * 2
def baseEnd_4164544 : Nat := 2138412778797859436147617

theorem tailTrace_4164544 : CollatzResearch.WordTrace tailWord_4164544 prefixEnd_4164544 2138412778797859436147617 := by
  unfold tailWord_4164544
  simp only [CollatzResearch.WordTrace]
  refine ⟨75946699112287905167502343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101262265483050540223336457 75946699112287905167502343)
  ·
    refine ⟨113920048668431857751253515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75946699112287905167502343 113920048668431857751253515)
    ·
      refine ⟨170880073002647786626880273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113920048668431857751253515 170880073002647786626880273)
      ·
        refine ⟨128160054751985839970160205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170880073002647786626880273 128160054751985839970160205)
        ·
          refine ⟨48060020531994689988810077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128160054751985839970160205 48060020531994689988810077)
          ·
            refine ⟨18022507699498008745803779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48060020531994689988810077 18022507699498008745803779)
            ·
              refine ⟨27033761549247013118705669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18022507699498008745803779 27033761549247013118705669)
              ·
                refine ⟨5068830290483814959757313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27033761549247013118705669 5068830290483814959757313)
                ·
                  refine ⟨3801622717862861219817985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5068830290483814959757313 3801622717862861219817985)
                  ·
                    refine ⟨2851217038397145914863489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3801622717862861219817985 2851217038397145914863489)
                    ·
                      refine ⟨2138412778797859436147617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851217038397145914863489 2138412778797859436147617)
                      ·
                        rfl

theorem cell23_4164544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_4164544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164544 prefixEnd_4164544 := by exact prefixLift 4164544
  have htrace : WordTrace (prefixWord ++ tailWord_4164544) baseStart_4164544 baseEnd_4164544 := by
    simpa [prefixWord, tailWord_4164544, baseEnd_4164544] using wordTrace_append hprefix tailTrace_4164544
  have hstable : (prefixWord ++ tailWord_4164544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164544).length < 2 ^ (prefixWord ++ tailWord_4164544).sum := by decide
  have hdescent : baseEnd_4164544 < baseStart_4164544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164580 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_4164580 : Nat := 118140960795 + 4164580 * 2 ^ 59
def prefixEnd_4164580 : Nat := 4983230072969 + 3 ^ 40 * 4164580 * 2
def baseEnd_4164580 : Nat := 712810421367140431765817

theorem tailTrace_4164580 : CollatzResearch.WordTrace tailWord_4164580 prefixEnd_4164580 712810421367140431765817 := by
  unfold tailWord_4164580
  simp only [CollatzResearch.WordTrace]
  refine ⟨75947355626222694241657597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101263140834963592322210129 75947355626222694241657597)
  ·
    refine ⟨28480258359833510340621599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75947355626222694241657597 28480258359833510340621599)
    ·
      refine ⟨42720387539750265510932399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28480258359833510340621599 42720387539750265510932399)
      ·
        refine ⟨64080581309625398266398599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42720387539750265510932399 64080581309625398266398599)
        ·
          refine ⟨96120871964438097399597899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64080581309625398266398599 96120871964438097399597899)
          ·
            refine ⟨144181307946657146099396849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96120871964438097399597899 144181307946657146099396849)
            ·
              refine ⟨108135980959992859574547637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144181307946657146099396849 108135980959992859574547637)
              ·
                refine ⟨10137748214999330585113841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108135980959992859574547637 10137748214999330585113841)
                ·
                  refine ⟨7603311161249497938835381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10137748214999330585113841 7603311161249497938835381)
                  ·
                    refine ⟨712810421367140431765817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7603311161249497938835381 712810421367140431765817)
                    ·
                      rfl

theorem cell23_4164580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_4164580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164580 prefixEnd_4164580 := by exact prefixLift 4164580
  have htrace : WordTrace (prefixWord ++ tailWord_4164580) baseStart_4164580 baseEnd_4164580 := by
    simpa [prefixWord, tailWord_4164580, baseEnd_4164580] using wordTrace_append hprefix tailTrace_4164580
  have hstable : (prefixWord ++ tailWord_4164580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164580).length < 2 ^ (prefixWord ++ tailWord_4164580).sum := by decide
  have hdescent : baseEnd_4164580 < baseStart_4164580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164600 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_4164600 : Nat := 118140960795 + 4164600 * 2 ^ 59
def prefixEnd_4164600 : Nat := 4983230072969 + 3 ^ 40 * 4164600 * 2
def baseEnd_4164600 : Nat := 2138441533714511217047359

theorem tailTrace_4164600 : CollatzResearch.WordTrace tailWord_4164600 prefixEnd_4164600 2138441533714511217047359 := by
  unfold tailWord_4164600
  simp only [CollatzResearch.WordTrace]
  refine ⟨75947720356186465949521627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101263627141581954599362169 75947720356186465949521627)
  ·
    refine ⟨113921580534279698924282441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75947720356186465949521627 113921580534279698924282441)
    ·
      refine ⟨85441185400709774193211831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113921580534279698924282441 85441185400709774193211831)
      ·
        refine ⟨128161778101064661289817747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85441185400709774193211831 128161778101064661289817747)
        ·
          refine ⟨192242667151596991934726621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128161778101064661289817747 192242667151596991934726621)
          ·
            refine ⟨72091000181848871975522483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192242667151596991934726621 72091000181848871975522483)
            ·
              refine ⟨108136500272773307963283725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72091000181848871975522483 108136500272773307963283725)
              ·
                refine ⟨40551187602289990486231397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108136500272773307963283725 40551187602289990486231397)
                ·
                  refine ⟨7603347675429373216168387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40551187602289990486231397 7603347675429373216168387)
                  ·
                    refine ⟨11405021513144059824252581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7603347675429373216168387 11405021513144059824252581)
                    ·
                      refine ⟨2138441533714511217047359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11405021513144059824252581 2138441533714511217047359)
                      ·
                        rfl

theorem cell23_4164600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_4164600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164600 prefixEnd_4164600 := by exact prefixLift 4164600
  have htrace : WordTrace (prefixWord ++ tailWord_4164600) baseStart_4164600 baseEnd_4164600 := by
    simpa [prefixWord, tailWord_4164600, baseEnd_4164600] using wordTrace_append hprefix tailTrace_4164600
  have hstable : (prefixWord ++ tailWord_4164600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164600).length < 2 ^ (prefixWord ++ tailWord_4164600).sum := by decide
  have hdescent : baseEnd_4164600 < baseStart_4164600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164654 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_4164654 : Nat := 118140960795 + 4164654 * 2 ^ 59
def prefixEnd_4164654 : Nat := 4983230072969 + 3 ^ 40 * 4164654 * 2
def baseEnd_4164654 : Nat := 2138469261669854005772111

theorem tailTrace_4164654 : CollatzResearch.WordTrace tailWord_4164654 prefixEnd_4164654 2138469261669854005772111 := by
  unfold tailWord_4164654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18987176281772162390188627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101264940169451532747672677 18987176281772162390188627)
  ·
    refine ⟨28480764422658243585282941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18987176281772162390188627 28480764422658243585282941)
    ·
      refine ⟨10680286658496841344481103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28480764422658243585282941 10680286658496841344481103)
      ·
        refine ⟨16020429987745262016721655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680286658496841344481103 16020429987745262016721655)
        ·
          refine ⟨24030644981617893025082483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16020429987745262016721655 24030644981617893025082483)
          ·
            refine ⟨36045967472426839537623725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24030644981617893025082483 36045967472426839537623725)
            ·
              refine ⟨13517237802160064826608897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36045967472426839537623725 13517237802160064826608897)
              ·
                refine ⟨10137928351620048619956673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13517237802160064826608897 10137928351620048619956673)
                ·
                  refine ⟨7603446263715036464967505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10137928351620048619956673 7603446263715036464967505)
                  ·
                    refine ⟨5702584697786277348725629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7603446263715036464967505 5702584697786277348725629)
                    ·
                      refine ⟨2138469261669854005772111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5702584697786277348725629 2138469261669854005772111)
                      ·
                        rfl

theorem cell23_4164654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_4164654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164654 prefixEnd_4164654 := by exact prefixLift 4164654
  have htrace : WordTrace (prefixWord ++ tailWord_4164654) baseStart_4164654 baseEnd_4164654 := by
    simpa [prefixWord, tailWord_4164654, baseEnd_4164654] using wordTrace_append hprefix tailTrace_4164654
  have hstable : (prefixWord ++ tailWord_4164654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164654).length < 2 ^ (prefixWord ++ tailWord_4164654).sum := by decide
  have hdescent : baseEnd_4164654 < baseStart_4164654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164677 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 3, 5, 2]
def baseStart_4164677 : Nat := 118140960795 + 4164677 * 2 ^ 59
def prefixEnd_4164677 : Nat := 4983230072969 + 3 ^ 40 * 4164677 * 2
def baseEnd_4164677 : Nat := 2138481071724907415784505

theorem tailTrace_4164677 : CollatzResearch.WordTrace tailWord_4164677 prefixEnd_4164677 2138481071724907415784505 := by
  unfold tailWord_4164677
  simp only [CollatzResearch.WordTrace]
  refine ⟨151898249133093974049596285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101265499422062649366397523 151898249133093974049596285)
  ·
    refine ⟨56961843424910240268598607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151898249133093974049596285 56961843424910240268598607)
    ·
      refine ⟨85442765137365360402897911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56961843424910240268598607 85442765137365360402897911)
      ·
        refine ⟨128164147706048040604346867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85442765137365360402897911 128164147706048040604346867)
        ·
          refine ⟨192246221559072060906520301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128164147706048040604346867 192246221559072060906520301)
          ·
            refine ⟨72092333084652022839945113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192246221559072060906520301 72092333084652022839945113)
            ·
              refine ⟨54069249813489017129958835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72092333084652022839945113 54069249813489017129958835)
              ·
                refine ⟨81103874720233525694938253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54069249813489017129958835 81103874720233525694938253)
                ·
                  refine ⟨30413953020087572135601845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81103874720233525694938253 30413953020087572135601845)
                  ·
                    refine ⟨2851308095633209887712673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30413953020087572135601845 2851308095633209887712673)
                    ·
                      refine ⟨2138481071724907415784505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851308095633209887712673 2138481071724907415784505)
                      ·
                        rfl

theorem cell23_4164677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_4164677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164677 prefixEnd_4164677 := by exact prefixLift 4164677
  have htrace : WordTrace (prefixWord ++ tailWord_4164677) baseStart_4164677 baseEnd_4164677 := by
    simpa [prefixWord, tailWord_4164677, baseEnd_4164677] using wordTrace_append hprefix tailTrace_4164677
  have hstable : (prefixWord ++ tailWord_4164677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164677).length < 2 ^ (prefixWord ++ tailWord_4164677).sum := by decide
  have hdescent : baseEnd_4164677 < baseStart_4164677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164704 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 1, 5]
def baseStart_4164704 : Nat := 118140960795 + 4164704 * 2 ^ 59
def prefixEnd_4164704 : Nat := 4983230072969 + 3 ^ 40 * 4164704 * 2
def baseEnd_4164704 : Nat := 712831645234192936715627

theorem tailTrace_4164704 : CollatzResearch.WordTrace tailWord_4164704 prefixEnd_4164704 712831645234192936715627 := by
  unfold tailWord_4164704
  simp only [CollatzResearch.WordTrace]
  refine ⟨75949616951998078830414583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101266155935997438440552777 75949616951998078830414583)
  ·
    refine ⟨113924425427997118245621875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75949616951998078830414583 113924425427997118245621875)
    ·
      refine ⟨170886638141995677368432813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113924425427997118245621875 170886638141995677368432813)
      ·
        refine ⟨64082489303248379013162305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170886638141995677368432813 64082489303248379013162305)
        ·
          refine ⟨48061866977436284259871729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64082489303248379013162305 48061866977436284259871729)
          ·
            refine ⟨36046400233077213194903797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48061866977436284259871729 36046400233077213194903797)
            ·
              refine ⟨3379350021850988737022231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36046400233077213194903797 3379350021850988737022231)
              ·
                refine ⟨5069025032776483105533347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379350021850988737022231 5069025032776483105533347)
                ·
                  refine ⟨7603537549164724658300021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069025032776483105533347 7603537549164724658300021)
                  ·
                    refine ⟨712831645234192936715627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7603537549164724658300021 712831645234192936715627)
                    ·
                      rfl

theorem cell23_4164704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 5].length) (baseStart_4164704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164704 prefixEnd_4164704 := by exact prefixLift 4164704
  have htrace : WordTrace (prefixWord ++ tailWord_4164704) baseStart_4164704 baseEnd_4164704 := by
    simpa [prefixWord, tailWord_4164704, baseEnd_4164704] using wordTrace_append hprefix tailTrace_4164704
  have hstable : (prefixWord ++ tailWord_4164704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164704).length < 2 ^ (prefixWord ++ tailWord_4164704).sum := by decide
  have hdescent : baseEnd_4164704 < baseStart_4164704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164712 : List Nat := [2, 1, 4, 4, 2, 1, 2, 2, 1, 4]
def baseStart_4164712 : Nat := 118140960795 + 4164712 * 2 ^ 59
def prefixEnd_4164712 : Nat := 4983230072969 + 3 ^ 40 * 4164712 * 2
def baseEnd_4164712 : Nat := 712833014515938259615615

theorem tailTrace_4164712 : CollatzResearch.WordTrace tailWord_4164712 prefixEnd_4164712 712833014515938259615615 := by
  unfold tailWord_4164712
  simp only [CollatzResearch.WordTrace]
  refine ⟨75949762843983587513560195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101266350458644783351413593 75949762843983587513560195)
  ·
    refine ⟨113924644265975381270340293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75949762843983587513560195 113924644265975381270340293)
    ·
      refine ⟨21360870799870383988188805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113924644265975381270340293 21360870799870383988188805)
      ·
        refine ⟨4005163274975696997785401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21360870799870383988188805 4005163274975696997785401)
        ·
          refine ⟨3003872456231772748339051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4005163274975696997785401 3003872456231772748339051)
          ·
            refine ⟨4505808684347659122508577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003872456231772748339051 4505808684347659122508577)
            ·
              refine ⟨3379356513260744341881433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4505808684347659122508577 3379356513260744341881433)
              ·
                refine ⟨2534517384945558256411075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379356513260744341881433 2534517384945558256411075)
                ·
                  refine ⟨3801776077418337384616613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534517384945558256411075 3801776077418337384616613)
                  ·
                    refine ⟨712833014515938259615615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3801776077418337384616613 712833014515938259615615)
                    ·
                      rfl

theorem cell23_4164712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_4164712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164712 prefixEnd_4164712 := by exact prefixLift 4164712
  have htrace : WordTrace (prefixWord ++ tailWord_4164712) baseStart_4164712 baseEnd_4164712 := by
    simpa [prefixWord, tailWord_4164712, baseEnd_4164712] using wordTrace_append hprefix tailTrace_4164712
  have hstable : (prefixWord ++ tailWord_4164712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164712).length < 2 ^ (prefixWord ++ tailWord_4164712).sum := by decide
  have hdescent : baseEnd_4164712 < baseStart_4164712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164718 : List Nat := [4, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_4164718 : Nat := 118140960795 + 4164718 * 2 ^ 59
def prefixEnd_4164718 : Nat := 4983230072969 + 3 ^ 40 * 4164718 * 2
def baseEnd_4164718 : Nat := 2138502124431741755371817

theorem tailTrace_4164718 : CollatzResearch.WordTrace tailWord_4164718 prefixEnd_4164718 2138502124431741755371817 := by
  unfold tailWord_4164718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18987468065743179756479851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101266496350630292034559205 18987468065743179756479851)
  ·
    refine ⟨28481202098614769634719777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18987468065743179756479851 28481202098614769634719777)
    ·
      refine ⟨21360901573961077226039833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28481202098614769634719777 21360901573961077226039833)
      ·
        refine ⟨16020676180470807919529875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21360901573961077226039833 16020676180470807919529875)
        ·
          refine ⟨24031014270706211879294813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16020676180470807919529875 24031014270706211879294813)
          ·
            refine ⟨9011630351514829454735555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24031014270706211879294813 9011630351514829454735555)
            ·
              refine ⟨13517445527272244182103333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9011630351514829454735555 13517445527272244182103333)
              ·
                refine ⟨2534521036363545784144375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13517445527272244182103333 2534521036363545784144375)
                ·
                  refine ⟨3801781554545318676216563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534521036363545784144375 3801781554545318676216563)
                  ·
                    refine ⟨5702672331817978014324845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3801781554545318676216563 5702672331817978014324845)
                    ·
                      refine ⟨2138502124431741755371817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5702672331817978014324845 2138502124431741755371817)
                      ·
                        rfl

theorem cell23_4164718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_4164718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164718 prefixEnd_4164718 := by exact prefixLift 4164718
  have htrace : WordTrace (prefixWord ++ tailWord_4164718) baseStart_4164718 baseEnd_4164718 := by
    simpa [prefixWord, tailWord_4164718, baseEnd_4164718] using wordTrace_append hprefix tailTrace_4164718
  have hstable : (prefixWord ++ tailWord_4164718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164718).length < 2 ^ (prefixWord ++ tailWord_4164718).sum := by decide
  have hdescent : baseEnd_4164718 < baseStart_4164718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164727 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_4164727 : Nat := 118140960795 + 4164727 * 2 ^ 59
def prefixEnd_4164727 : Nat := 4983230072969 + 3 ^ 40 * 4164727 * 2
def baseEnd_4164727 : Nat := 2138506745757632220159275

theorem tailTrace_4164727 : CollatzResearch.WordTrace tailWord_4164727 prefixEnd_4164727 2138506745757632220159275 := by
  unfold tailWord_4164727
  simp only [CollatzResearch.WordTrace]
  refine ⟨151900072782912832588916435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101266715188608555059277623 151900072782912832588916435)
  ·
    refine ⟨227850109174369248883374653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151900072782912832588916435 227850109174369248883374653)
    ·
      refine ⟨85443790940388468331265495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227850109174369248883374653 85443790940388468331265495)
      ·
        refine ⟨128165686410582702496898243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85443790940388468331265495 128165686410582702496898243)
        ·
          refine ⟨192248529615874053745347365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128165686410582702496898243 192248529615874053745347365)
          ·
            refine ⟨36046599302976385077252631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192248529615874053745347365 36046599302976385077252631)
            ·
              refine ⟨54069898954464577615878947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36046599302976385077252631 54069898954464577615878947)
              ·
                refine ⟨81104848431696866423818421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54069898954464577615878947 81104848431696866423818421)
                ·
                  refine ⟨7603579540471581227232977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81104848431696866423818421 7603579540471581227232977)
                  ·
                    refine ⟨5702684655353685920424733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7603579540471581227232977 5702684655353685920424733)
                    ·
                      refine ⟨2138506745757632220159275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5702684655353685920424733 2138506745757632220159275)
                      ·
                        rfl

theorem cell23_4164727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_4164727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164727 prefixEnd_4164727 := by exact prefixLift 4164727
  have htrace : WordTrace (prefixWord ++ tailWord_4164727) baseStart_4164727 baseEnd_4164727 := by
    simpa [prefixWord, tailWord_4164727, baseEnd_4164727] using wordTrace_append hprefix tailTrace_4164727
  have hstable : (prefixWord ++ tailWord_4164727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164727).length < 2 ^ (prefixWord ++ tailWord_4164727).sum := by decide
  have hdescent : baseEnd_4164727 < baseStart_4164727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164754 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4164754 : Nat := 118140960795 + 4164754 * 2 ^ 59
def prefixEnd_4164754 : Nat := 4983230072969 + 3 ^ 40 * 4164754 * 2
def baseEnd_4164754 : Nat := 2138520609735303614521651

theorem tailTrace_4164754 : CollatzResearch.WordTrace tailWord_4164754 prefixEnd_4164754 2138520609735303614521651 := by
  unfold tailWord_4164754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37975264388453754050037329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101267371702543344133432877 37975264388453754050037329)
  ·
    refine ⟨28481448291340315537527997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37975264388453754050037329 28481448291340315537527997)
    ·
      refine ⟨10680543109252618326572999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28481448291340315537527997 10680543109252618326572999)
      ·
        refine ⟨16020814663878927489859499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680543109252618326572999 16020814663878927489859499)
        ·
          refine ⟨24031221995818391234789249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16020814663878927489859499 24031221995818391234789249)
          ·
            refine ⟨18023416496863793426091937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24031221995818391234789249 18023416496863793426091937)
            ·
              refine ⟨13517562372647845069568953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18023416496863793426091937 13517562372647845069568953)
              ·
                refine ⟨10138171779485883802176715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13517562372647845069568953 10138171779485883802176715)
                ·
                  refine ⟨15207257669228825703265073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10138171779485883802176715 15207257669228825703265073)
                  ·
                    refine ⟨11405443251921619277448805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15207257669228825703265073 11405443251921619277448805)
                    ·
                      refine ⟨2138520609735303614521651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11405443251921619277448805 2138520609735303614521651)
                      ·
                        rfl

theorem cell23_4164754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4164754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164754 prefixEnd_4164754 := by exact prefixLift 4164754
  have htrace : WordTrace (prefixWord ++ tailWord_4164754) baseStart_4164754 baseEnd_4164754 := by
    simpa [prefixWord, tailWord_4164754, baseEnd_4164754] using wordTrace_append hprefix tailTrace_4164754
  have hstable : (prefixWord ++ tailWord_4164754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164754).length < 2 ^ (prefixWord ++ tailWord_4164754).sum := by decide
  have hdescent : baseEnd_4164754 < baseStart_4164754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164757 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_4164757 : Nat := 118140960795 + 4164757 * 2 ^ 59
def prefixEnd_4164757 : Nat := 4983230072969 + 3 ^ 40 * 4164757 * 2
def baseEnd_4164757 : Nat := 2138522150177267102784137

theorem tailTrace_4164757 : CollatzResearch.WordTrace tailWord_4164757 prefixEnd_4164757 2138522150177267102784137 := by
  unfold tailWord_4164757
  simp only [CollatzResearch.WordTrace]
  refine ⟨151901166972804147712508525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101267444648536098475005683 151901166972804147712508525)
  ·
    refine ⟨56962937614801555392190697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151901166972804147712508525 56962937614801555392190697)
    ·
      refine ⟨42722203211101166544143023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56962937614801555392190697 42722203211101166544143023)
      ·
        refine ⟨64083304816651749816214535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42722203211101166544143023 64083304816651749816214535)
        ·
          refine ⟨96124957224977624724321803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64083304816651749816214535 96124957224977624724321803)
          ·
            refine ⟨144187435837466437086482705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96124957224977624724321803 144187435837466437086482705)
            ·
              refine ⟨108140576878099827814862029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144187435837466437086482705 108140576878099827814862029)
              ·
                refine ⟨40552716329287435430573261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108140576878099827814862029 40552716329287435430573261)
                ·
                  refine ⟨15207268623482788286464973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40552716329287435430573261 15207268623482788286464973)
                  ·
                    refine ⟨5702725733806045607424365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15207268623482788286464973 5702725733806045607424365)
                    ·
                      refine ⟨2138522150177267102784137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5702725733806045607424365 2138522150177267102784137)
                      ·
                        rfl

theorem cell23_4164757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_4164757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164757 prefixEnd_4164757 := by exact prefixLift 4164757
  have htrace : WordTrace (prefixWord ++ tailWord_4164757) baseStart_4164757 baseEnd_4164757 := by
    simpa [prefixWord, tailWord_4164757, baseEnd_4164757] using wordTrace_append hprefix tailTrace_4164757
  have hstable : (prefixWord ++ tailWord_4164757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164757).length < 2 ^ (prefixWord ++ tailWord_4164757).sum := by decide
  have hdescent : baseEnd_4164757 < baseStart_4164757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164775 : List Nat := [1, 1, 6, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_4164775 : Nat := 118140960795 + 4164775 * 2 ^ 59
def prefixEnd_4164775 : Nat := 4983230072969 + 3 ^ 40 * 4164775 * 2
def baseEnd_4164775 : Nat := 2138531392829048032359055

theorem tailTrace_4164775 : CollatzResearch.WordTrace tailWord_4164775 prefixEnd_4164775 2138531392829048032359055 := by
  unfold tailWord_4164775
  simp only [CollatzResearch.WordTrace]
  refine ⟨151901823486738936786663779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101267882324492624524442519 151901823486738936786663779)
  ·
    refine ⟨227852735230108405179995669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151901823486738936786663779 227852735230108405179995669)
    ·
      refine ⟨10680596963911331492812297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227852735230108405179995669 10680596963911331492812297)
      ·
        refine ⟨8010447722933498619609223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10680596963911331492812297 8010447722933498619609223)
        ·
          refine ⟨12015671584400247929413835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8010447722933498619609223 12015671584400247929413835)
          ·
            refine ⟨18023507376600371894120753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12015671584400247929413835 18023507376600371894120753)
            ·
              refine ⟨13517630532450278920590565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18023507376600371894120753 13517630532450278920590565)
              ·
                refine ⟨2534555724834427297610731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13517630532450278920590565 2534555724834427297610731)
                ·
                  refine ⟨3801833587251640946416097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534555724834427297610731 3801833587251640946416097)
                  ·
                    refine ⟨2851375190438730709812073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3801833587251640946416097 2851375190438730709812073)
                    ·
                      refine ⟨2138531392829048032359055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851375190438730709812073 2138531392829048032359055)
                      ·
                        rfl

theorem cell23_4164775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_4164775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164775 prefixEnd_4164775 := by exact prefixLift 4164775
  have htrace : WordTrace (prefixWord ++ tailWord_4164775) baseStart_4164775 baseEnd_4164775 := by
    simpa [prefixWord, tailWord_4164775, baseEnd_4164775] using wordTrace_append hprefix tailTrace_4164775
  have hstable : (prefixWord ++ tailWord_4164775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164775).length < 2 ^ (prefixWord ++ tailWord_4164775).sum := by decide
  have hdescent : baseEnd_4164775 < baseStart_4164775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164797 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_4164797 : Nat := 118140960795 + 4164797 * 2 ^ 59
def prefixEnd_4164797 : Nat := 4983230072969 + 3 ^ 40 * 4164797 * 2
def baseEnd_4164797 : Nat := 2138542689403446946283953

theorem tailTrace_4164797 : CollatzResearch.WordTrace tailWord_4164797 prefixEnd_4164797 2138542689403446946283953 := by
  unfold tailWord_4164797
  simp only [CollatzResearch.WordTrace]
  refine ⟨151902625892659234543964645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101268417261772823029309763 151902625892659234543964645)
  ·
    refine ⟨28481742354873606476993371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151902625892659234543964645 28481742354873606476993371)
    ·
      refine ⟨42722613532310409715490057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28481742354873606476993371 42722613532310409715490057)
      ·
        refine ⟨32041960149232807286617543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42722613532310409715490057 32041960149232807286617543)
        ·
          refine ⟨48062940223849210929926315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32041960149232807286617543 48062940223849210929926315)
          ·
            refine ⟨72094410335773816394889473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48062940223849210929926315 72094410335773816394889473)
            ·
              refine ⟨54070807751830362296167105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72094410335773816394889473 54070807751830362296167105)
              ·
                refine ⟨40553105813872771722125329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54070807751830362296167105 40553105813872771722125329)
                ·
                  refine ⟨30414829360404578791593997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40553105813872771722125329 30414829360404578791593997)
                  ·
                    refine ⟨11405561010151717046847749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30414829360404578791593997 11405561010151717046847749)
                    ·
                      refine ⟨2138542689403446946283953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11405561010151717046847749 2138542689403446946283953)
                      ·
                        rfl

theorem cell23_4164797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_4164797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164797 prefixEnd_4164797 := by exact prefixLift 4164797
  have htrace : WordTrace (prefixWord ++ tailWord_4164797) baseStart_4164797 baseEnd_4164797 := by
    simpa [prefixWord, tailWord_4164797, baseEnd_4164797] using wordTrace_append hprefix tailTrace_4164797
  have hstable : (prefixWord ++ tailWord_4164797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164797).length < 2 ^ (prefixWord ++ tailWord_4164797).sum := by decide
  have hdescent : baseEnd_4164797 < baseStart_4164797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164817 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_4164817 : Nat := 118140960795 + 4164817 * 2 ^ 59
def prefixEnd_4164817 : Nat := 4983230072969 + 3 ^ 40 * 4164817 * 2
def baseEnd_4164817 : Nat := 2138552959016536868033861

theorem tailTrace_4164817 : CollatzResearch.WordTrace tailWord_4164817 prefixEnd_4164817 2138552959016536868033861 := by
  unfold tailWord_4164817
  simp only [CollatzResearch.WordTrace]
  refine ⟨151903355352586777959692705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101268903568391185306461803 151903355352586777959692705)
  ·
    refine ⟨113927516514440083469769529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151903355352586777959692705 113927516514440083469769529)
    ·
      refine ⟨85445637385830062602327147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113927516514440083469769529 85445637385830062602327147)
      ·
        refine ⟨128168456078745093903490721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85445637385830062602327147 128168456078745093903490721)
        ·
          refine ⟨96126342059058820427618041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128168456078745093903490721 96126342059058820427618041)
          ·
            refine ⟨72094756544294115320713531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96126342059058820427618041 72094756544294115320713531)
            ·
              refine ⟨108142134816441172981070297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72094756544294115320713531 108142134816441172981070297)
              ·
                refine ⟨81106601112330879735802723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108142134816441172981070297 81106601112330879735802723)
                ·
                  refine ⟨121659901668496319603704085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81106601112330879735802723 121659901668496319603704085)
                  ·
                    refine ⟨5702807890710764981423629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121659901668496319603704085 5702807890710764981423629)
                    ·
                      refine ⟨2138552959016536868033861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5702807890710764981423629 2138552959016536868033861)
                      ·
                        rfl

theorem cell23_4164817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_4164817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164817 prefixEnd_4164817 := by exact prefixLift 4164817
  have htrace : WordTrace (prefixWord ++ tailWord_4164817) baseStart_4164817 baseEnd_4164817 := by
    simpa [prefixWord, tailWord_4164817, baseEnd_4164817] using wordTrace_append hprefix tailTrace_4164817
  have hstable : (prefixWord ++ tailWord_4164817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164817).length < 2 ^ (prefixWord ++ tailWord_4164817).sum := by decide
  have hdescent : baseEnd_4164817 < baseStart_4164817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164831 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 4, 2, 2]
def baseStart_4164831 : Nat := 118140960795 + 4164831 * 2 ^ 59
def prefixEnd_4164831 : Nat := 4983230072969 + 3 ^ 40 * 4164831 * 2
def baseEnd_4164831 : Nat := 2138560147745699813258797

theorem tailTrace_4164831 : CollatzResearch.WordTrace tailWord_4164831 prefixEnd_4164831 2138560147745699813258797 := by
  unfold tailWord_4164831
  simp only [CollatzResearch.WordTrace]
  refine ⟨151903865974536058350702347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101269243983024038900468231 151903865974536058350702347)
  ·
    refine ⟨227855798961804087526053521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151903865974536058350702347 227855798961804087526053521)
    ·
      refine ⟨170891849221353065644540141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227855798961804087526053521 170891849221353065644540141)
      ·
        refine ⟨64084443458007399616702553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170891849221353065644540141 64084443458007399616702553)
        ·
          refine ⟨48063332593505549712526915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64084443458007399616702553 48063332593505549712526915)
          ·
            refine ⟨72094998890258324568790373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48063332593505549712526915 72094998890258324568790373)
            ·
              refine ⟨13517812291923435856648195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72094998890258324568790373 13517812291923435856648195)
              ·
                refine ⟨20276718437885153784972293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13517812291923435856648195 20276718437885153784972293)
                ·
                  refine ⟨3801884707103466334682305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20276718437885153784972293 3801884707103466334682305)
                  ·
                    refine ⟨2851413530327599751011729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3801884707103466334682305 2851413530327599751011729)
                    ·
                      refine ⟨2138560147745699813258797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851413530327599751011729 2138560147745699813258797)
                      ·
                        rfl

theorem cell23_4164831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_4164831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164831 prefixEnd_4164831 := by exact prefixLift 4164831
  have htrace : WordTrace (prefixWord ++ tailWord_4164831) baseStart_4164831 baseEnd_4164831 := by
    simpa [prefixWord, tailWord_4164831, baseEnd_4164831] using wordTrace_append hprefix tailTrace_4164831
  have hstable : (prefixWord ++ tailWord_4164831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164831).length < 2 ^ (prefixWord ++ tailWord_4164831).sum := by decide
  have hdescent : baseEnd_4164831 < baseStart_4164831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164852 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4164852 : Nat := 118140960795 + 4164852 * 2 ^ 59
def prefixEnd_4164852 : Nat := 4983230072969 + 3 ^ 40 * 4164852 * 2
def baseEnd_4164852 : Nat := 2138570930839444231096201

theorem tailTrace_4164852 : CollatzResearch.WordTrace tailWord_4164852 prefixEnd_4164852 2138570930839444231096201 := by
  unfold tailWord_4164852
  simp only [CollatzResearch.WordTrace]
  refine ⟨75952315953729989468608405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101269754604973319291477873 75952315953729989468608405)
  ·
    refine ⟨3560264810331093256341019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75952315953729989468608405 3560264810331093256341019)
    ·
      refine ⟨5340397215496639884511529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3560264810331093256341019 5340397215496639884511529)
      ·
        refine ⟨4005297911622479913383647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5340397215496639884511529 4005297911622479913383647)
        ·
          refine ⟨6007946867433719870075471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005297911622479913383647 6007946867433719870075471)
          ·
            refine ⟨9011920301150579805113207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007946867433719870075471 9011920301150579805113207)
            ·
              refine ⟨13517880451725869707669811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9011920301150579805113207 13517880451725869707669811)
              ·
                refine ⟨20276820677588804561504717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13517880451725869707669811 20276820677588804561504717)
                ·
                  refine ⟨7603807754095801710564269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20276820677588804561504717 7603807754095801710564269)
                  ·
                    refine ⟨2851427907785925641461601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7603807754095801710564269 2851427907785925641461601)
                    ·
                      refine ⟨2138570930839444231096201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851427907785925641461601 2138570930839444231096201)
                      ·
                        rfl

theorem cell23_4164852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4164852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164852 prefixEnd_4164852 := by exact prefixLift 4164852
  have htrace : WordTrace (prefixWord ++ tailWord_4164852) baseStart_4164852 baseEnd_4164852 := by
    simpa [prefixWord, tailWord_4164852, baseEnd_4164852] using wordTrace_append hprefix tailTrace_4164852
  have hstable : (prefixWord ++ tailWord_4164852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164852).length < 2 ^ (prefixWord ++ tailWord_4164852).sum := by decide
  have hdescent : baseEnd_4164852 < baseStart_4164852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164888 : List Nat := [2, 1, 2, 3, 1, 5, 2, 2, 5]
def baseStart_4164888 : Nat := 118140960795 + 4164888 * 2 ^ 59
def prefixEnd_4164888 : Nat := 4983230072969 + 3 ^ 40 * 4164888 * 2
def baseEnd_4164888 : Nat := 237621046238111787805115

theorem tailTrace_4164888 : CollatzResearch.WordTrace tailWord_4164888 prefixEnd_4164888 237621046238111787805115 := by
  unfold tailWord_4164888
  simp only [CollatzResearch.WordTrace]
  refine ⟨75952972467664778542763659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101270629956886371390351545 75952972467664778542763659)
  ·
    refine ⟨113929458701497167814145489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75952972467664778542763659 113929458701497167814145489)
    ·
      refine ⟨85447094026122875860609117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113929458701497167814145489 85447094026122875860609117)
      ·
        refine ⟨32042660259796078447728419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85447094026122875860609117 32042660259796078447728419)
        ·
          refine ⟨48063990389694117671592629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32042660259796078447728419 48063990389694117671592629)
          ·
            refine ⟨4505999099033823531711809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48063990389694117671592629 4505999099033823531711809)
            ·
              refine ⟨3379499324275367648783857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4505999099033823531711809 3379499324275367648783857)
              ·
                refine ⟨2534624493206525736587893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379499324275367648783857 2534624493206525736587893)
                ·
                  refine ⟨237621046238111787805115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2534624493206525736587893 237621046238111787805115)
                  ·
                    rfl

theorem cell23_4164888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 5].length) (baseStart_4164888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164888 prefixEnd_4164888 := by exact prefixLift 4164888
  have htrace : WordTrace (prefixWord ++ tailWord_4164888) baseStart_4164888 baseEnd_4164888 := by
    simpa [prefixWord, tailWord_4164888, baseEnd_4164888] using wordTrace_append hprefix tailTrace_4164888
  have hstable : (prefixWord ++ tailWord_4164888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164888).length < 2 ^ (prefixWord ++ tailWord_4164888).sum := by decide
  have hdescent : baseEnd_4164888 < baseStart_4164888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164897 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 2, 8]
def baseStart_4164897 : Nat := 118140960795 + 4164897 * 2 ^ 59
def prefixEnd_4164897 : Nat := 4983230072969 + 3 ^ 40 * 4164897 * 2
def baseEnd_4164897 : Nat := 712864679156298851677831

theorem tailTrace_4164897 : CollatzResearch.WordTrace tailWord_4164897 prefixEnd_4164897 712864679156298851677831 := by
  unfold tailWord_4164897
  simp only [CollatzResearch.WordTrace]
  refine ⟨151906273192296951622604945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101270848794864634415069963 151906273192296951622604945)
  ·
    refine ⟨113929704894222713716953709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151906273192296951622604945 113929704894222713716953709)
    ·
      refine ⟨42723639335333517643857641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113929704894222713716953709 42723639335333517643857641)
      ·
        refine ⟨32042729501500138232893231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42723639335333517643857641 32042729501500138232893231)
        ·
          refine ⟨48064094252250207349339847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32042729501500138232893231 48064094252250207349339847)
          ·
            refine ⟨72096141378375311024009771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48064094252250207349339847 72096141378375311024009771)
            ·
              refine ⟨108144212067562966536014657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72096141378375311024009771 108144212067562966536014657)
              ·
                refine ⟨81108159050672224902010993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108144212067562966536014657 81108159050672224902010993)
                ·
                  refine ⟨60831119288004168676508245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81108159050672224902010993 60831119288004168676508245)
                  ·
                    refine ⟨712864679156298851677831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60831119288004168676508245 712864679156298851677831)
                    ·
                      rfl

theorem cell23_4164897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_4164897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164897 prefixEnd_4164897 := by exact prefixLift 4164897
  have htrace : WordTrace (prefixWord ++ tailWord_4164897) baseStart_4164897 baseEnd_4164897 := by
    simpa [prefixWord, tailWord_4164897, baseEnd_4164897] using wordTrace_append hprefix tailTrace_4164897
  have hstable : (prefixWord ++ tailWord_4164897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164897).length < 2 ^ (prefixWord ++ tailWord_4164897).sum := by decide
  have hdescent : baseEnd_4164897 < baseStart_4164897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164918 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_4164918 : Nat := 118140960795 + 4164918 * 2 ^ 59
def prefixEnd_4164918 : Nat := 4983230072969 + 3 ^ 40 * 4164918 * 2
def baseEnd_4164918 : Nat := 712868273520880324290299

theorem tailTrace_4164918 : CollatzResearch.WordTrace tailWord_4164918 prefixEnd_4164918 712868273520880324290299 := by
  unfold tailWord_4164918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494189945326304513069963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101271359416813914806079605 9494189945326304513069963)
  ·
    refine ⟨14241284917989456769604945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9494189945326304513069963 14241284917989456769604945)
    ·
      refine ⟨10680963688492092577203709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14241284917989456769604945 10680963688492092577203709)
      ·
        refine ⟨4005361383184534716451391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10680963688492092577203709 4005361383184534716451391)
        ·
          refine ⟨6008042074776802074677087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005361383184534716451391 6008042074776802074677087)
          ·
            refine ⟨9012063112165203112015631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008042074776802074677087 9012063112165203112015631)
            ·
              refine ⟨13518094668247804668023447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9012063112165203112015631 13518094668247804668023447)
              ·
                refine ⟨20277142002371707002035171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13518094668247804668023447 20277142002371707002035171)
                ·
                  refine ⟨30415713003557560503052757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20277142002371707002035171 30415713003557560503052757)
                  ·
                    refine ⟨712868273520880324290299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30415713003557560503052757 712868273520880324290299)
                    ·
                      rfl

theorem cell23_4164918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_4164918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164918 prefixEnd_4164918 := by exact prefixLift 4164918
  have htrace : WordTrace (prefixWord ++ tailWord_4164918) baseStart_4164918 baseEnd_4164918 := by
    simpa [prefixWord, tailWord_4164918, baseEnd_4164918] using wordTrace_append hprefix tailTrace_4164918
  have hstable : (prefixWord ++ tailWord_4164918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164918).length < 2 ^ (prefixWord ++ tailWord_4164918).sum := by decide
  have hdescent : baseEnd_4164918 < baseStart_4164918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164921 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4164921 : Nat := 118140960795 + 4164921 * 2 ^ 59
def prefixEnd_4164921 : Nat := 4983230072969 + 3 ^ 40 * 4164921 * 2
def baseEnd_4164921 : Nat := 2138606361004604461133383

theorem tailTrace_4164921 : CollatzResearch.WordTrace tailWord_4164921 prefixEnd_4164921 2138606361004604461133383 := by
  unfold tailWord_4164921
  simp only [CollatzResearch.WordTrace]
  refine ⟨151907148544210003721478617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101271432362806669147652411 151907148544210003721478617)
  ·
    refine ⟨113930361408157502791108963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151907148544210003721478617 113930361408157502791108963)
    ·
      refine ⟨170895542112236254186663445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113930361408157502791108963 170895542112236254186663445)
      ·
        refine ⟨8010728536511074414999849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170895542112236254186663445 8010728536511074414999849)
        ·
          refine ⟨6008046402383305811249887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8010728536511074414999849 6008046402383305811249887)
          ·
            refine ⟨9012069603574958716874831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008046402383305811249887 9012069603574958716874831)
            ·
              refine ⟨13518104405362438075312247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9012069603574958716874831 13518104405362438075312247)
              ·
                refine ⟨20277156608043657112968371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13518104405362438075312247 20277156608043657112968371)
                ·
                  refine ⟨30415734912065485669452557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20277156608043657112968371 30415734912065485669452557)
                  ·
                    refine ⟨11405900592024557126044709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30415734912065485669452557 11405900592024557126044709)
                    ·
                      refine ⟨2138606361004604461133383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11405900592024557126044709 2138606361004604461133383)
                      ·
                        rfl

theorem cell23_4164921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4164921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164921 prefixEnd_4164921 := by exact prefixLift 4164921
  have htrace : WordTrace (prefixWord ++ tailWord_4164921) baseStart_4164921 baseEnd_4164921 := by
    simpa [prefixWord, tailWord_4164921, baseEnd_4164921] using wordTrace_append hprefix tailTrace_4164921
  have hstable : (prefixWord ++ tailWord_4164921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164921).length < 2 ^ (prefixWord ++ tailWord_4164921).sum := by decide
  have hdescent : baseEnd_4164921 < baseStart_4164921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164947 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 8]
def baseStart_4164947 : Nat := 118140960795 + 4164947 * 2 ^ 59
def prefixEnd_4164947 : Nat := 4983230072969 + 3 ^ 40 * 4164947 * 2
def baseEnd_4164947 : Nat := 2138619711501621359408263

theorem tailTrace_4164947 : CollatzResearch.WordTrace tailWord_4164947 prefixEnd_4164947 2138619711501621359408263 := by
  unfold tailWord_4164947
  simp only [CollatzResearch.WordTrace]
  refine ⟨151908096842115810161925095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101272064561410540107950063 151908096842115810161925095)
  ·
    refine ⟨227862145263173715242887643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151908096842115810161925095 227862145263173715242887643)
    ·
      refine ⟨341793217894760572864331465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227862145263173715242887643 341793217894760572864331465)
      ·
        refine ⟨256344913421070429648248599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341793217894760572864331465 256344913421070429648248599)
        ·
          refine ⟨384517370131605644472372899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256344913421070429648248599 384517370131605644472372899)
          ·
            refine ⟨576776055197408466708559349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384517370131605644472372899 576776055197408466708559349)
            ·
              refine ⟨54072755174757043753927439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 576776055197408466708559349 54072755174757043753927439)
              ·
                refine ⟨81109132762135565630891159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54072755174757043753927439 81109132762135565630891159)
                ·
                  refine ⟨121663699143203348446336739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81109132762135565630891159 121663699143203348446336739)
                  ·
                    refine ⟨182495548714805022669505109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121663699143203348446336739 182495548714805022669505109)
                    ·
                      refine ⟨2138619711501621359408263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 182495548714805022669505109 2138619711501621359408263)
                      ·
                        rfl

theorem cell23_4164947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_4164947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164947 prefixEnd_4164947 := by exact prefixLift 4164947
  have htrace : WordTrace (prefixWord ++ tailWord_4164947) baseStart_4164947 baseEnd_4164947 := by
    simpa [prefixWord, tailWord_4164947, baseEnd_4164947] using wordTrace_append hprefix tailTrace_4164947
  have hstable : (prefixWord ++ tailWord_4164947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164947).length < 2 ^ (prefixWord ++ tailWord_4164947).sum := by decide
  have hdescent : baseEnd_4164947 < baseStart_4164947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4164948 : List Nat := [2, 4, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_4164948 : Nat := 118140960795 + 4164948 * 2 ^ 59
def prefixEnd_4164948 : Nat := 4983230072969 + 3 ^ 40 * 4164948 * 2
def baseEnd_4164948 : Nat := 712873408327425285165253

theorem tailTrace_4164948 : CollatzResearch.WordTrace tailWord_4164948 prefixEnd_4164948 712873408327425285165253 := by
  unfold tailWord_4164948
  simp only [CollatzResearch.WordTrace]
  refine ⟨75954066657556093666355749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101272088876741458221807665 75954066657556093666355749)
  ·
    refine ⟨14241387498291767562441703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75954066657556093666355749 14241387498291767562441703)
    ·
      refine ⟨21362081247437651343662555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14241387498291767562441703 21362081247437651343662555)
      ·
        refine ⟨32043121871156477015493833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21362081247437651343662555 32043121871156477015493833)
        ·
          refine ⟨24032341403367357761620375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32043121871156477015493833 24032341403367357761620375)
          ·
            refine ⟨36048512105051036642430563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24032341403367357761620375 36048512105051036642430563)
            ·
              refine ⟨54072768157576554963645845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36048512105051036642430563 54072768157576554963645845)
              ·
                refine ⟨2534661007386401013920899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54072768157576554963645845 2534661007386401013920899)
                ·
                  refine ⟨3801991511079601520881349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2534661007386401013920899 3801991511079601520881349)
                  ·
                    refine ⟨712873408327425285165253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3801991511079601520881349 712873408327425285165253)
                    ·
                      rfl

theorem cell23_4164948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_4164948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4164948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4164948 prefixEnd_4164948 := by exact prefixLift 4164948
  have htrace : WordTrace (prefixWord ++ tailWord_4164948) baseStart_4164948 baseEnd_4164948 := by
    simpa [prefixWord, tailWord_4164948, baseEnd_4164948] using wordTrace_append hprefix tailTrace_4164948
  have hstable : (prefixWord ++ tailWord_4164948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4164948).length < 2 ^ (prefixWord ++ tailWord_4164948).sum := by decide
  have hdescent : baseEnd_4164948 < baseStart_4164948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4164948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165024 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_4165024 : Nat := 118140960795 + 4165024 * 2 ^ 59
def prefixEnd_4165024 : Nat := 4983230072969 + 3 ^ 40 * 4165024 * 2
def baseEnd_4165024 : Nat := 2138659249512017558145409

theorem tailTrace_4165024 : CollatzResearch.WordTrace tailWord_4165024 prefixEnd_4165024 2138659249512017558145409 := by
  unfold tailWord_4165024
  simp only [CollatzResearch.WordTrace]
  refine ⟨75955452631418426156239063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101273936841891234874985417 75955452631418426156239063)
  ·
    refine ⟨113933178947127639234358595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75955452631418426156239063 113933178947127639234358595)
    ·
      refine ⟨170899768420691458851537893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113933178947127639234358595 170899768420691458851537893)
      ·
        refine ⟨32043706578879648534663355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170899768420691458851537893 32043706578879648534663355)
        ·
          refine ⟨48065559868319472801995033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32043706578879648534663355 48065559868319472801995033)
          ·
            refine ⟨36049169901239604601496275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48065559868319472801995033 36049169901239604601496275)
            ·
              refine ⟨54073754851859406902244413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36049169901239604601496275 54073754851859406902244413)
              ·
                refine ⟨20277658069447277588341655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54073754851859406902244413 20277658069447277588341655)
                ·
                  refine ⟨30416487104170916382512483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20277658069447277588341655 30416487104170916382512483)
                  ·
                    refine ⟨45624730656256374573768725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30416487104170916382512483 45624730656256374573768725)
                    ·
                      refine ⟨2138659249512017558145409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45624730656256374573768725 2138659249512017558145409)
                      ·
                        rfl

theorem cell23_4165024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_4165024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165024 prefixEnd_4165024 := by exact prefixLift 4165024
  have htrace : WordTrace (prefixWord ++ tailWord_4165024) baseStart_4165024 baseEnd_4165024 := by
    simpa [prefixWord, tailWord_4165024, baseEnd_4165024] using wordTrace_append hprefix tailTrace_4165024
  have hstable : (prefixWord ++ tailWord_4165024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165024).length < 2 ^ (prefixWord ++ tailWord_4165024).sum := by decide
  have hdescent : baseEnd_4165024 < baseStart_4165024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165028 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_4165028 : Nat := 118140960795 + 4165028 * 2 ^ 59
def prefixEnd_4165028 : Nat := 4983230072969 + 3 ^ 40 * 4165028 * 2
def baseEnd_4165028 : Nat := 2138661303434635542495391

theorem tailTrace_4165028 : CollatzResearch.WordTrace tailWord_4165028 prefixEnd_4165028 2138661303434635542495391 := by
  unfold tailWord_4165028
  simp only [CollatzResearch.WordTrace]
  refine ⟨75955525577411180497811869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101274034103214907330415825 75955525577411180497811869)
  ·
    refine ⟨28483322091529192686679451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75955525577411180497811869 28483322091529192686679451)
    ·
      refine ⟨42724983137293789030019177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28483322091529192686679451 42724983137293789030019177)
      ·
        refine ⟨32043737352970341772514383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42724983137293789030019177 32043737352970341772514383)
        ·
          refine ⟨48065606029455512658771575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32043737352970341772514383 48065606029455512658771575)
          ·
            refine ⟨72098409044183268988157363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48065606029455512658771575 72098409044183268988157363)
            ·
              refine ⟨108147613566274903482236045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72098409044183268988157363 108147613566274903482236045)
              ·
                refine ⟨40555355087353088805838517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108147613566274903482236045 40555355087353088805838517)
                ·
                  refine ⟨3802064539439352075547361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40555355087353088805838517 3802064539439352075547361)
                  ·
                    refine ⟨2851548404579514056660521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3802064539439352075547361 2851548404579514056660521)
                    ·
                      refine ⟨2138661303434635542495391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851548404579514056660521 2138661303434635542495391)
                      ·
                        rfl

theorem cell23_4165028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_4165028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165028 prefixEnd_4165028 := by exact prefixLift 4165028
  have htrace : WordTrace (prefixWord ++ tailWord_4165028) baseStart_4165028 baseEnd_4165028 := by
    simpa [prefixWord, tailWord_4165028, baseEnd_4165028] using wordTrace_append hprefix tailTrace_4165028
  have hstable : (prefixWord ++ tailWord_4165028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165028).length < 2 ^ (prefixWord ++ tailWord_4165028).sum := by decide
  have hdescent : baseEnd_4165028 < baseStart_4165028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165032 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4165032 : Nat := 118140960795 + 4165032 * 2 ^ 59
def prefixEnd_4165032 : Nat := 4983230072969 + 3 ^ 40 * 4165032 * 2
def baseEnd_4165032 : Nat := 2138663357357253526845373

theorem tailTrace_4165032 : CollatzResearch.WordTrace tailWord_4165032 prefixEnd_4165032 2138663357357253526845373 := by
  unfold tailWord_4165032
  simp only [CollatzResearch.WordTrace]
  refine ⟨75955598523403934839384675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101274131364538579785846233 75955598523403934839384675)
  ·
    refine ⟨113933397785105902259077013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75955598523403934839384675 113933397785105902259077013)
    ·
      refine ⟨5340628021176839168394235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113933397785105902259077013 5340628021176839168394235)
      ·
        refine ⟨8010942031765258752591353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5340628021176839168394235 8010942031765258752591353)
        ·
          refine ⟨6008206523823944064443515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8010942031765258752591353 6008206523823944064443515)
          ·
            refine ⟨9012309785735916096665273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008206523823944064443515 9012309785735916096665273)
            ·
              refine ⟨6759232339301937072498955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9012309785735916096665273 6759232339301937072498955)
              ·
                refine ⟨10138848508952905608748433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6759232339301937072498955 10138848508952905608748433)
                ·
                  refine ⟨7604136381714679206561325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10138848508952905608748433 7604136381714679206561325)
                  ·
                    refine ⟨2851551143143004702460497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7604136381714679206561325 2851551143143004702460497)
                    ·
                      refine ⟨2138663357357253526845373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851551143143004702460497 2138663357357253526845373)
                      ·
                        rfl

theorem cell23_4165032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4165032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165032 prefixEnd_4165032 := by exact prefixLift 4165032
  have htrace : WordTrace (prefixWord ++ tailWord_4165032) baseStart_4165032 baseEnd_4165032 := by
    simpa [prefixWord, tailWord_4165032, baseEnd_4165032] using wordTrace_append hprefix tailTrace_4165032
  have hstable : (prefixWord ++ tailWord_4165032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165032).length < 2 ^ (prefixWord ++ tailWord_4165032).sum := by decide
  have hdescent : baseEnd_4165032 < baseStart_4165032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165041 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4165041 : Nat := 118140960795 + 4165041 * 2 ^ 59
def prefixEnd_4165041 : Nat := 4983230072969 + 3 ^ 40 * 4165041 * 2
def baseEnd_4165041 : Nat := 2138667978683143991632831

theorem tailTrace_4165041 : CollatzResearch.WordTrace tailWord_4165041 prefixEnd_4165041 2138667978683143991632831 := by
  unfold tailWord_4165041
  simp only [CollatzResearch.WordTrace]
  refine ⟨151911525303775264215846977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101274350202516842810564651 151911525303775264215846977)
  ·
    refine ⟨113933643977831448161885233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151911525303775264215846977 113933643977831448161885233)
    ·
      refine ⟨85450232983373586121413925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113933643977831448161885233 85450232983373586121413925)
      ·
        refine ⟨16021918684382547397765111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85450232983373586121413925 16021918684382547397765111)
        ·
          refine ⟨24032878026573821096647667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16021918684382547397765111 24032878026573821096647667)
          ·
            refine ⟨36049317039860731644971501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24032878026573821096647667 36049317039860731644971501)
            ·
              refine ⟨13518493889947774366864313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36049317039860731644971501 13518493889947774366864313)
              ·
                refine ⟨10138870417460830775148235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13518493889947774366864313 10138870417460830775148235)
                ·
                  refine ⟨15208305626191246162722353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10138870417460830775148235 15208305626191246162722353)
                  ·
                    refine ⟨11406229219643434622041765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15208305626191246162722353 11406229219643434622041765)
                    ·
                      refine ⟨2138667978683143991632831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11406229219643434622041765 2138667978683143991632831)
                      ·
                        rfl

theorem cell23_4165041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4165041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165041 prefixEnd_4165041 := by exact prefixLift 4165041
  have htrace : WordTrace (prefixWord ++ tailWord_4165041) baseStart_4165041 baseEnd_4165041 := by
    simpa [prefixWord, tailWord_4165041, baseEnd_4165041] using wordTrace_append hprefix tailTrace_4165041
  have hstable : (prefixWord ++ tailWord_4165041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165041).length < 2 ^ (prefixWord ++ tailWord_4165041).sum := by decide
  have hdescent : baseEnd_4165041 < baseStart_4165041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165045 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_4165045 : Nat := 118140960795 + 4165045 * 2 ^ 59
def prefixEnd_4165045 : Nat := 4983230072969 + 3 ^ 40 * 4165045 * 2
def baseEnd_4165045 : Nat := 2138670032605761975982813

theorem tailTrace_4165045 : CollatzResearch.WordTrace tailWord_4165045 prefixEnd_4165045 2138670032605761975982813 := by
  unfold tailWord_4165045
  simp only [CollatzResearch.WordTrace]
  refine ⟨151911671195760772898992589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101274447463840515265995059 151911671195760772898992589)
  ·
    refine ⟨56966876698410289837122221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151911671195760772898992589 56966876698410289837122221)
    ·
      refine ⟨21362578761903858688920833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56966876698410289837122221 21362578761903858688920833)
      ·
        refine ⟨16021934071427894016690625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21362578761903858688920833 16021934071427894016690625)
        ·
          refine ⟨12016450553570920512517969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16021934071427894016690625 12016450553570920512517969)
          ·
            refine ⟨9012337915178190384388477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12016450553570920512517969 9012337915178190384388477)
            ·
              refine ⟨3379626718191821394145679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9012337915178190384388477 3379626718191821394145679)
              ·
                refine ⟨5069440077287732091218519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379626718191821394145679 5069440077287732091218519)
                ·
                  refine ⟨7604160115931598136827779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069440077287732091218519 7604160115931598136827779)
                  ·
                    refine ⟨11406240173897397205241669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7604160115931598136827779 11406240173897397205241669)
                    ·
                      refine ⟨2138670032605761975982813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11406240173897397205241669 2138670032605761975982813)
                      ·
                        rfl

theorem cell23_4165045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_4165045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165045 prefixEnd_4165045 := by exact prefixLift 4165045
  have htrace : WordTrace (prefixWord ++ tailWord_4165045) baseStart_4165045 baseEnd_4165045 := by
    simpa [prefixWord, tailWord_4165045, baseEnd_4165045] using wordTrace_append hprefix tailTrace_4165045
  have hstable : (prefixWord ++ tailWord_4165045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165045).length < 2 ^ (prefixWord ++ tailWord_4165045).sum := by decide
  have hdescent : baseEnd_4165045 < baseStart_4165045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165064 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 1, 9]
def baseStart_4165064 : Nat := 118140960795 + 4165064 * 2 ^ 59
def prefixEnd_4165064 : Nat := 4983230072969 + 3 ^ 40 * 4165064 * 2
def baseEnd_4165064 : Nat := 712893262912732467215075

theorem tailTrace_4165064 : CollatzResearch.WordTrace tailWord_4165064 prefixEnd_4165064 712893262912732467215075 := by
  unfold tailWord_4165064
  simp only [CollatzResearch.WordTrace]
  refine ⟨75956182091345969571967123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101274909455127959429289497 75956182091345969571967123)
  ·
    refine ⟨113934273137018954357950685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75956182091345969571967123 113934273137018954357950685)
    ·
      refine ⟨42725352426382107884231507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113934273137018954357950685 42725352426382107884231507)
      ·
        refine ⟨64088028639573161826347261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42725352426382107884231507 64088028639573161826347261)
        ·
          refine ⟨24033010739839935684880223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64088028639573161826347261 24033010739839935684880223)
          ·
            refine ⟨36049516109759903527320335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24033010739839935684880223 36049516109759903527320335)
            ·
              refine ⟨54074274164639855290980503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36049516109759903527320335 54074274164639855290980503)
              ·
                refine ⟨81111411246959782936470755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54074274164639855290980503 81111411246959782936470755)
                ·
                  refine ⟨121667116870439674404706133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81111411246959782936470755 121667116870439674404706133)
                  ·
                    refine ⟨712893262912732467215075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 121667116870439674404706133 712893262912732467215075)
                    ·
                      rfl

theorem cell23_4165064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_4165064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165064 prefixEnd_4165064 := by exact prefixLift 4165064
  have htrace : WordTrace (prefixWord ++ tailWord_4165064) baseStart_4165064 baseEnd_4165064 := by
    simpa [prefixWord, tailWord_4165064, baseEnd_4165064] using wordTrace_append hprefix tailTrace_4165064
  have hstable : (prefixWord ++ tailWord_4165064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165064).length < 2 ^ (prefixWord ++ tailWord_4165064).sum := by decide
  have hdescent : baseEnd_4165064 < baseStart_4165064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165105 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 1, 3, 2]
def baseStart_4165105 : Nat := 118140960795 + 4165105 * 2 ^ 59
def prefixEnd_4165105 : Nat := 4983230072969 + 3 ^ 40 * 4165105 * 2
def baseEnd_4165105 : Nat := 2138700841445031741232537

theorem tailTrace_4165105 : CollatzResearch.WordTrace tailWord_4165105 prefixEnd_4165105 2138700841445031741232537 := by
  unfold tailWord_4165105
  simp only [CollatzResearch.WordTrace]
  refine ⟨151913859575543403146176769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101275906383695602097451179 151913859575543403146176769)
  ·
    refine ⟨113935394681657552359632577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151913859575543403146176769 113935394681657552359632577)
    ·
      refine ⟨85451546011243164269724433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113935394681657552359632577 85451546011243164269724433)
      ·
        refine ⟨64088659508432373202293325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85451546011243164269724433 64088659508432373202293325)
        ·
          refine ⟨24033247315662139950859997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64088659508432373202293325 24033247315662139950859997)
          ·
            refine ⟨9012467743373302481572499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24033247315662139950859997 9012467743373302481572499)
            ·
              refine ⟨13518701615059953722358749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9012467743373302481572499 13518701615059953722358749)
              ·
                refine ⟨5069513105647482645884531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13518701615059953722358749 5069513105647482645884531)
                ·
                  refine ⟨7604269658471223968826797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069513105647482645884531 7604269658471223968826797)
                  ·
                    refine ⟨2851601121926708988310049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7604269658471223968826797 2851601121926708988310049)
                    ·
                      refine ⟨2138700841445031741232537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851601121926708988310049 2138700841445031741232537)
                      ·
                        rfl

theorem cell23_4165105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_4165105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165105 prefixEnd_4165105 := by exact prefixLift 4165105
  have htrace : WordTrace (prefixWord ++ tailWord_4165105) baseStart_4165105 baseEnd_4165105 := by
    simpa [prefixWord, tailWord_4165105, baseEnd_4165105] using wordTrace_append hprefix tailTrace_4165105
  have hstable : (prefixWord ++ tailWord_4165105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165105).length < 2 ^ (prefixWord ++ tailWord_4165105).sum := by decide
  have hdescent : baseEnd_4165105 < baseStart_4165105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165126 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_4165126 : Nat := 118140960795 + 4165126 * 2 ^ 59
def prefixEnd_4165126 : Nat := 4983230072969 + 3 ^ 40 * 4165126 * 2
def baseEnd_4165126 : Nat := 2138711624538776159069941

theorem tailTrace_4165126 : CollatzResearch.WordTrace tailWord_4165126 prefixEnd_4165126 2138711624538776159069941 := by
  unfold tailWord_4165126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4747332047139603866646601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101276417005644882488460821 4747332047139603866646601)
  ·
    refine ⟨3560499035354702899984951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4747332047139603866646601 3560499035354702899984951)
    ·
      refine ⟨5340748553032054349977427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3560499035354702899984951 5340748553032054349977427)
      ·
        refine ⟨8011122829548081524966141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5340748553032054349977427 8011122829548081524966141)
        ·
          refine ⟨3004171061080530571862303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8011122829548081524966141 3004171061080530571862303)
          ·
            refine ⟨4506256591620795857793455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004171061080530571862303 4506256591620795857793455)
            ·
              refine ⟨6759384887431193786690183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506256591620795857793455 6759384887431193786690183)
              ·
                refine ⟨10139077331146790680035275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6759384887431193786690183 10139077331146790680035275)
                ·
                  refine ⟨15208615996720186020052913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139077331146790680035275 15208615996720186020052913)
                  ·
                    refine ⟨11406461997540139515039685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15208615996720186020052913 11406461997540139515039685)
                    ·
                      refine ⟨2138711624538776159069941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11406461997540139515039685 2138711624538776159069941)
                      ·
                        rfl

theorem cell23_4165126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_4165126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165126 prefixEnd_4165126 := by exact prefixLift 4165126
  have htrace : WordTrace (prefixWord ++ tailWord_4165126) baseStart_4165126 baseEnd_4165126 := by
    simpa [prefixWord, tailWord_4165126, baseEnd_4165126] using wordTrace_append hprefix tailTrace_4165126
  have hstable : (prefixWord ++ tailWord_4165126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165126).length < 2 ^ (prefixWord ++ tailWord_4165126).sum := by decide
  have hdescent : baseEnd_4165126 < baseStart_4165126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165141 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 7]
def baseStart_4165141 : Nat := 118140960795 + 4165141 * 2 ^ 59
def prefixEnd_4165141 : Nat := 4983230072969 + 3 ^ 40 * 4165141 * 2
def baseEnd_4165141 : Nat := 237635480749843733375819

theorem tailTrace_4165141 : CollatzResearch.WordTrace tailWord_4165141 prefixEnd_4165141 237635480749843733375819 := by
  unfold tailWord_4165141
  simp only [CollatzResearch.WordTrace]
  refine ⟨151915172603412981294487277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101276781735608654196324851 151915172603412981294487277)
  ·
    refine ⟨56968189726279867985432729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151915172603412981294487277 56968189726279867985432729)
    ·
      refine ⟨42726142294709900989074547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56968189726279867985432729 42726142294709900989074547)
      ·
        refine ⟨64089213442064851483611821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42726142294709900989074547 64089213442064851483611821)
        ·
          refine ⟨24033455040774319306354433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64089213442064851483611821 24033455040774319306354433)
          ·
            refine ⟨18025091280580739479765825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24033455040774319306354433 18025091280580739479765825)
            ·
              refine ⟨13518818460435554609824369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18025091280580739479765825 13518818460435554609824369)
              ·
                refine ⟨10139113845326665957368277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13518818460435554609824369 10139113845326665957368277)
                ·
                  refine ⟨237635480749843733375819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10139113845326665957368277 237635480749843733375819)
                  ·
                    rfl

theorem cell23_4165141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_4165141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165141 prefixEnd_4165141 := by exact prefixLift 4165141
  have htrace : WordTrace (prefixWord ++ tailWord_4165141) baseStart_4165141 baseEnd_4165141 := by
    simpa [prefixWord, tailWord_4165141, baseEnd_4165141] using wordTrace_append hprefix tailTrace_4165141
  have hstable : (prefixWord ++ tailWord_4165141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165141).length < 2 ^ (prefixWord ++ tailWord_4165141).sum := by decide
  have hdescent : baseEnd_4165141 < baseStart_4165141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165151 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 3]
def baseStart_4165151 : Nat := 118140960795 + 4165151 * 2 ^ 59
def prefixEnd_4165151 : Nat := 4983230072969 + 3 ^ 40 * 4165151 * 2
def baseEnd_4165151 : Nat := 2138724461555138561257325

theorem tailTrace_4165151 : CollatzResearch.WordTrace tailWord_4165151 prefixEnd_4165151 2138724461555138561257325 := by
  unfold tailWord_4165151
  simp only [CollatzResearch.WordTrace]
  refine ⟨151915537333376753002351307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101277024888917835334900871 151915537333376753002351307)
  ·
    refine ⟨227873306000065129503526961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151915537333376753002351307 227873306000065129503526961)
    ·
      refine ⟨170904979500048847127645221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227873306000065129503526961 170904979500048847127645221)
      ·
        refine ⟨32044683656259158836433479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170904979500048847127645221 32044683656259158836433479)
        ·
          refine ⟨48067025484388738254650219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32044683656259158836433479 48067025484388738254650219)
          ·
            refine ⟨72100538226583107381975329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48067025484388738254650219 72100538226583107381975329)
            ·
              refine ⟨54075403669937330536481497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72100538226583107381975329 54075403669937330536481497)
              ·
                refine ⟨40556552752452997902361123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54075403669937330536481497 40556552752452997902361123)
                ·
                  refine ⟨60834829128679496853541685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40556552752452997902361123 60834829128679496853541685)
                  ·
                    refine ⟨5703265230813702830019533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60834829128679496853541685 5703265230813702830019533)
                    ·
                      refine ⟨2138724461555138561257325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5703265230813702830019533 2138724461555138561257325)
                      ·
                        rfl

theorem cell23_4165151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_4165151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165151 prefixEnd_4165151 := by exact prefixLift 4165151
  have htrace : WordTrace (prefixWord ++ tailWord_4165151) baseStart_4165151 baseEnd_4165151 := by
    simpa [prefixWord, tailWord_4165151, baseEnd_4165151] using wordTrace_append hprefix tailTrace_4165151
  have hstable : (prefixWord ++ tailWord_4165151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165151).length < 2 ^ (prefixWord ++ tailWord_4165151).sum := by decide
  have hdescent : baseEnd_4165151 < baseStart_4165151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165171 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 4, 5]
def baseStart_4165171 : Nat := 118140960795 + 4165171 * 2 ^ 59
def prefixEnd_4165171 : Nat := 4983230072969 + 3 ^ 40 * 4165171 * 2
def baseEnd_4165171 : Nat := 712911577056076161002411

theorem tailTrace_4165171 : CollatzResearch.WordTrace tailWord_4165171 prefixEnd_4165171 712911577056076161002411 := by
  unfold tailWord_4165171
  simp only [CollatzResearch.WordTrace]
  refine ⟨151916266793304296418079367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101277511195536197612052911 151916266793304296418079367)
  ·
    refine ⟨227874400189956444627119051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151916266793304296418079367 227874400189956444627119051)
    ·
      refine ⟨341811600284934666940678577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227874400189956444627119051 341811600284934666940678577)
      ·
        refine ⟨256358700213701000205508933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341811600284934666940678577 256358700213701000205508933)
        ·
          refine ⟨48067256290068937538532925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256358700213701000205508933 48067256290068937538532925)
          ·
            refine ⟨18025221108775851576949847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48067256290068937538532925 18025221108775851576949847)
            ·
              refine ⟨27037831663163777365424771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18025221108775851576949847 27037831663163777365424771)
              ·
                refine ⟨40556747494745666048137157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27037831663163777365424771 40556747494745666048137157)
                ·
                  refine ⟨7604390155264812384025717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40556747494745666048137157 7604390155264812384025717)
                  ·
                    refine ⟨712911577056076161002411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7604390155264812384025717 712911577056076161002411)
                    ·
                      rfl

theorem cell23_4165171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 5].length) (baseStart_4165171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165171 prefixEnd_4165171 := by exact prefixLift 4165171
  have htrace : WordTrace (prefixWord ++ tailWord_4165171) baseStart_4165171 baseEnd_4165171 := by
    simpa [prefixWord, tailWord_4165171, baseEnd_4165171] using wordTrace_append hprefix tailTrace_4165171
  have hstable : (prefixWord ++ tailWord_4165171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165171).length < 2 ^ (prefixWord ++ tailWord_4165171).sum := by decide
  have hdescent : baseEnd_4165171 < baseStart_4165171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165175 : List Nat := [1, 1, 3, 1, 2, 5, 3, 2, 5]
def baseStart_4165175 : Nat := 118140960795 + 4165175 * 2 ^ 59
def prefixEnd_4165175 : Nat := 4983230072969 + 3 ^ 40 * 4165175 * 2
def baseEnd_4165175 : Nat := 237637420565649607484135

theorem tailTrace_4165175 : CollatzResearch.WordTrace tailWord_4165175 prefixEnd_4165175 237637420565649607484135 := by
  unfold tailWord_4165175
  simp only [CollatzResearch.WordTrace]
  refine ⟨151916412685289805101224979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101277608456859870067483319 151916412685289805101224979)
  ·
    refine ⟨227874619027934707651837469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151916412685289805101224979 227874619027934707651837469)
    ·
      refine ⟨85452982135475515369439051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227874619027934707651837469 85452982135475515369439051)
      ·
        refine ⟨128179473203213273054158577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85452982135475515369439051 128179473203213273054158577)
        ·
          refine ⟨96134604902409954790618933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128179473203213273054158577 96134604902409954790618933)
          ·
            refine ⟨9012619209600933261620525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96134604902409954790618933 9012619209600933261620525)
            ·
              refine ⟨3379732203600349973107697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9012619209600933261620525 3379732203600349973107697)
              ·
                refine ⟨2534799152700262479830773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379732203600349973107697 2534799152700262479830773)
                ·
                  refine ⟨237637420565649607484135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2534799152700262479830773 237637420565649607484135)
                  ·
                    rfl

theorem cell23_4165175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 5].length) (baseStart_4165175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165175 prefixEnd_4165175 := by exact prefixLift 4165175
  have htrace : WordTrace (prefixWord ++ tailWord_4165175) baseStart_4165175 baseEnd_4165175 := by
    simpa [prefixWord, tailWord_4165175, baseEnd_4165175] using wordTrace_append hprefix tailTrace_4165175
  have hstable : (prefixWord ++ tailWord_4165175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165175).length < 2 ^ (prefixWord ++ tailWord_4165175).sum := by decide
  have hdescent : baseEnd_4165175 < baseStart_4165175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165178 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2]
def baseStart_4165178 : Nat := 118140960795 + 4165178 * 2 ^ 59
def prefixEnd_4165178 : Nat := 4983230072969 + 3 ^ 40 * 4165178 * 2
def baseEnd_4165178 : Nat := 2138738325532809955619701

theorem tailTrace_4165178 : CollatzResearch.WordTrace tailWord_4165178 prefixEnd_4165178 2138738325532809955619701 := by
  unfold tailWord_4165178
  simp only [CollatzResearch.WordTrace]
  refine ⟨37979130526069734153396047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101277681402852624409056125 37979130526069734153396047)
  ·
    refine ⟨56968695789104601230094071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37979130526069734153396047 56968695789104601230094071)
    ·
      refine ⟨85453043683656901845141107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56968695789104601230094071 85453043683656901845141107)
      ·
        refine ⟨128179565525485352767711661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85453043683656901845141107 128179565525485352767711661)
        ·
          refine ⟨48067337072057007287891873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128179565525485352767711661 48067337072057007287891873)
          ·
            refine ⟨36050502804042755465918905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48067337072057007287891873 36050502804042755465918905)
            ·
              refine ⟨27037877103032066599439179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36050502804042755465918905 27037877103032066599439179)
              ·
                refine ⟨40556815654548099899158769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27037877103032066599439179 40556815654548099899158769)
                ·
                  refine ⟨30417611740911074924369077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40556815654548099899158769 30417611740911074924369077)
                  ·
                    refine ⟨2851651100710413274159601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30417611740911074924369077 2851651100710413274159601)
                    ·
                      refine ⟨2138738325532809955619701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851651100710413274159601 2138738325532809955619701)
                      ·
                        rfl

theorem cell23_4165178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_4165178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165178 prefixEnd_4165178 := by exact prefixLift 4165178
  have htrace : WordTrace (prefixWord ++ tailWord_4165178) baseStart_4165178 baseEnd_4165178 := by
    simpa [prefixWord, tailWord_4165178, baseEnd_4165178] using wordTrace_append hprefix tailTrace_4165178
  have hstable : (prefixWord ++ tailWord_4165178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165178).length < 2 ^ (prefixWord ++ tailWord_4165178).sum := by decide
  have hdescent : baseEnd_4165178 < baseStart_4165178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165208 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 4, 4, 2]
def baseStart_4165208 : Nat := 118140960795 + 4165208 * 2 ^ 59
def prefixEnd_4165208 : Nat := 4983230072969 + 3 ^ 40 * 4165208 * 2
def baseEnd_4165208 : Nat := 2138753729952444838244563

theorem tailTrace_4165208 : CollatzResearch.WordTrace tailWord_4165208 prefixEnd_4165208 2138753729952444838244563 := by
  unfold tailWord_4165208
  simp only [CollatzResearch.WordTrace]
  refine ⟨75958808147085125868588139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101278410862780167824784185 75958808147085125868588139)
  ·
    refine ⟨113938212220627688802882209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75958808147085125868588139 113938212220627688802882209)
    ·
      refine ⟨85453659165470766602161657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113938212220627688802882209 85453659165470766602161657)
      ·
        refine ⟨64090244374103074951621243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85453659165470766602161657 64090244374103074951621243)
        ·
          refine ⟨96135366561154612427431865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64090244374103074951621243 96135366561154612427431865)
          ·
            refine ⟨72101524920865959320573899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96135366561154612427431865 72101524920865959320573899)
            ·
              refine ⟨108152287381298938980860849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72101524920865959320573899 108152287381298938980860849)
              ·
                refine ⟨81114215535974204235645637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108152287381298938980860849 81114215535974204235645637)
                ·
                  refine ⟨15208915412995163294183557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81114215535974204235645637 15208915412995163294183557)
                  ·
                    refine ⟨2851671639936593117659417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15208915412995163294183557 2851671639936593117659417)
                    ·
                      refine ⟨2138753729952444838244563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851671639936593117659417 2138753729952444838244563)
                      ·
                        rfl

theorem cell23_4165208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_4165208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165208 prefixEnd_4165208 := by exact prefixLift 4165208
  have htrace : WordTrace (prefixWord ++ tailWord_4165208) baseStart_4165208 baseEnd_4165208 := by
    simpa [prefixWord, tailWord_4165208, baseEnd_4165208] using wordTrace_append hprefix tailTrace_4165208
  have hstable : (prefixWord ++ tailWord_4165208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165208).length < 2 ^ (prefixWord ++ tailWord_4165208).sum := by decide
  have hdescent : baseEnd_4165208 < baseStart_4165208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165262 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_4165262 : Nat := 118140960795 + 4165262 * 2 ^ 59
def prefixEnd_4165262 : Nat := 4983230072969 + 3 ^ 40 * 4165262 * 2
def baseEnd_4165262 : Nat := 2138781457907787626969315

theorem tailTrace_4165262 : CollatzResearch.WordTrace tailWord_4165262 prefixEnd_4165262 2138781457907787626969315 := by
  unfold tailWord_4165262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18989948229496827369955255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101279723890649745973094693 18989948229496827369955255)
  ·
    refine ⟨28484922344245241054932883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18989948229496827369955255 28484922344245241054932883)
    ·
      refine ⟨42727383516367861582399325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28484922344245241054932883 42727383516367861582399325)
      ·
        refine ⟨16022768818637948093399747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42727383516367861582399325 16022768818637948093399747)
        ·
          refine ⟨24034153227956922140099621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16022768818637948093399747 24034153227956922140099621)
          ·
            refine ⟨4506403730241922901268679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24034153227956922140099621 4506403730241922901268679)
            ·
              refine ⟨6759605595362884351903019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506403730241922901268679 6759605595362884351903019)
              ·
                refine ⟨10139408393044326527854529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6759605595362884351903019 10139408393044326527854529)
                ·
                  refine ⟨7604556294783244895890897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10139408393044326527854529 7604556294783244895890897)
                  ·
                    refine ⟨5703417221087433671918173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7604556294783244895890897 5703417221087433671918173)
                    ·
                      refine ⟨2138781457907787626969315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5703417221087433671918173 2138781457907787626969315)
                      ·
                        rfl

theorem cell23_4165262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_4165262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165262 prefixEnd_4165262 := by exact prefixLift 4165262
  have htrace : WordTrace (prefixWord ++ tailWord_4165262) baseStart_4165262 baseEnd_4165262 := by
    simpa [prefixWord, tailWord_4165262, baseEnd_4165262] using wordTrace_append hprefix tailTrace_4165262
  have hstable : (prefixWord ++ tailWord_4165262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165262).length < 2 ^ (prefixWord ++ tailWord_4165262).sum := by decide
  have hdescent : baseEnd_4165262 < baseStart_4165262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165285 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 2, 3, 2]
def baseStart_4165285 : Nat := 118140960795 + 4165285 * 2 ^ 59
def prefixEnd_4165285 : Nat := 4983230072969 + 3 ^ 40 * 4165285 * 2
def baseEnd_4165285 : Nat := 2138793267962841036981709

theorem tailTrace_4165285 : CollatzResearch.WordTrace tailWord_4165285 prefixEnd_4165285 2138793267962841036981709 := by
  unfold tailWord_4165285
  simp only [CollatzResearch.WordTrace]
  refine ⟨151920424714891293887729309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101280283143260862591819539 151920424714891293887729309)
  ·
    refine ⟨56970159268084235207898491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151920424714891293887729309 56970159268084235207898491)
    ·
      refine ⟨85455238902126352811847737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56970159268084235207898491 85455238902126352811847737)
      ·
        refine ⟨64091429176594764608885803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85455238902126352811847737 64091429176594764608885803)
        ·
          refine ⟨96137143764892146913328705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64091429176594764608885803 96137143764892146913328705)
          ·
            refine ⟨72102857823669110184996529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96137143764892146913328705 72102857823669110184996529)
            ·
              refine ⟨54077143367751832638747397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72102857823669110184996529 54077143367751832638747397)
              ·
                refine ⟨10139464381453468619765137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54077143367751832638747397 10139464381453468619765137)
                ·
                  refine ⟨7604598286090101464823853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10139464381453468619765137 7604598286090101464823853)
                  ·
                    refine ⟨2851724357283788049308945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7604598286090101464823853 2851724357283788049308945)
                    ·
                      refine ⟨2138793267962841036981709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2851724357283788049308945 2138793267962841036981709)
                      ·
                        rfl

theorem cell23_4165285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_4165285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165285 prefixEnd_4165285 := by exact prefixLift 4165285
  have htrace : WordTrace (prefixWord ++ tailWord_4165285) baseStart_4165285 baseEnd_4165285 := by
    simpa [prefixWord, tailWord_4165285, baseEnd_4165285] using wordTrace_append hprefix tailTrace_4165285
  have hstable : (prefixWord ++ tailWord_4165285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165285).length < 2 ^ (prefixWord ++ tailWord_4165285).sum := by decide
  have hdescent : baseEnd_4165285 < baseStart_4165285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165298 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_4165298 : Nat := 118140960795 + 4165298 * 2 ^ 59
def prefixEnd_4165298 : Nat := 4983230072969 + 3 ^ 40 * 4165298 * 2
def baseEnd_4165298 : Nat := 2138799943211349486119149

theorem tailTrace_4165298 : CollatzResearch.WordTrace tailWord_4165298 prefixEnd_4165298 2138799943211349486119149 := by
  unfold tailWord_4165298
  simp only [CollatzResearch.WordTrace]
  refine ⟨37980224715961049276988137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101280599242562798071968365 37980224715961049276988137)
  ·
    refine ⟨28485168536970786957741103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37980224715961049276988137 28485168536970786957741103)
    ·
      refine ⟨42727752805456180436611655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28485168536970786957741103 42727752805456180436611655)
      ·
        refine ⟨64091629208184270654917483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42727752805456180436611655 64091629208184270654917483)
        ·
          refine ⟨96137443812276405982376225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64091629208184270654917483 96137443812276405982376225)
          ·
            refine ⟨72103082859207304486782169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96137443812276405982376225 72103082859207304486782169)
            ·
              refine ⟨54077312144405478365086627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72103082859207304486782169 54077312144405478365086627)
              ·
                refine ⟨81115968216608217547629941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54077312144405478365086627 81115968216608217547629941)
                ·
                  refine ⟨7604622020307020395090307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81115968216608217547629941 7604622020307020395090307)
                  ·
                    refine ⟨11406933030460530592635461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7604622020307020395090307 11406933030460530592635461)
                    ·
                      refine ⟨2138799943211349486119149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11406933030460530592635461 2138799943211349486119149)
                      ·
                        rfl

theorem cell23_4165298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_4165298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165298 prefixEnd_4165298 := by exact prefixLift 4165298
  have htrace : WordTrace (prefixWord ++ tailWord_4165298) baseStart_4165298 baseEnd_4165298 := by
    simpa [prefixWord, tailWord_4165298, baseEnd_4165298] using wordTrace_append hprefix tailTrace_4165298
  have hstable : (prefixWord ++ tailWord_4165298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165298).length < 2 ^ (prefixWord ++ tailWord_4165298).sum := by decide
  have hdescent : baseEnd_4165298 < baseStart_4165298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165331 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 7]
def baseStart_4165331 : Nat := 118140960795 + 4165331 * 2 ^ 59
def prefixEnd_4165331 : Nat := 4983230072969 + 3 ^ 40 * 4165331 * 2
def baseEnd_4165331 : Nat := 2138816888072947857006497

theorem tailTrace_4165331 : CollatzResearch.WordTrace tailWord_4165331 prefixEnd_4165331 2138816888072947857006497 := by
  unfold tailWord_4165331
  simp only [CollatzResearch.WordTrace]
  refine ⟨151922102472724643743903847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101281401648483095829269231 151922102472724643743903847)
  ·
    refine ⟨227883153709086965615855771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151922102472724643743903847 227883153709086965615855771)
    ·
      refine ⟨341824730563630448423783657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227883153709086965615855771 341824730563630448423783657)
      ·
        refine ⟨256368547922722836317837743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341824730563630448423783657 256368547922722836317837743)
        ·
          refine ⟨384552821884084254476756615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256368547922722836317837743 384552821884084254476756615)
          ·
            refine ⟨576829232826126381715134923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384552821884084254476756615 576829232826126381715134923)
            ·
              refine ⟨865243849239189572572702385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576829232826126381715134923 865243849239189572572702385)
              ·
                refine ⟨648932886929392179429526789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865243849239189572572702385 648932886929392179429526789)
                ·
                  refine ⟨121674916299261033643036273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648932886929392179429526789 121674916299261033643036273)
                  ·
                    refine ⟨91256187224445775232277205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121674916299261033643036273 91256187224445775232277205)
                    ·
                      refine ⟨2138816888072947857006497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91256187224445775232277205 2138816888072947857006497)
                      ·
                        rfl

theorem cell23_4165331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_4165331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165331 prefixEnd_4165331 := by exact prefixLift 4165331
  have htrace : WordTrace (prefixWord ++ tailWord_4165331) baseStart_4165331 baseEnd_4165331 := by
    simpa [prefixWord, tailWord_4165331, baseEnd_4165331] using wordTrace_append hprefix tailTrace_4165331
  have hstable : (prefixWord ++ tailWord_4165331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165331).length < 2 ^ (prefixWord ++ tailWord_4165331).sum := by decide
  have hdescent : baseEnd_4165331 < baseStart_4165331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165332 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4165332 : Nat := 118140960795 + 4165332 * 2 ^ 59
def prefixEnd_4165332 : Nat := 4983230072969 + 3 ^ 40 * 4165332 * 2
def baseEnd_4165332 : Nat := 2138817401553602353093993

theorem tailTrace_4165332 : CollatzResearch.WordTrace tailWord_4165332 prefixEnd_4165332 2138817401553602353093993 := by
  unfold tailWord_4165332
  simp only [CollatzResearch.WordTrace]
  refine ⟨75961069472860510457345125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101281425963814013943126833 75961069472860510457345125)
  ·
    refine ⟨14242700526161345710752211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75961069472860510457345125 14242700526161345710752211)
    ·
      refine ⟨21364050789242018566128317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14242700526161345710752211 21364050789242018566128317)
      ·
        refine ⟨8011519045965756962298119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21364050789242018566128317 8011519045965756962298119)
        ·
          refine ⟨12017278568948635443447179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8011519045965756962298119 12017278568948635443447179)
          ·
            refine ⟨18025917853422953165170769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12017278568948635443447179 18025917853422953165170769)
            ·
              refine ⟨13519438390067214873878077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18025917853422953165170769 13519438390067214873878077)
              ·
                refine ⟨5069789396275205577704279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13519438390067214873878077 5069789396275205577704279)
                ·
                  refine ⟨7604684094412808366556419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069789396275205577704279 7604684094412808366556419)
                  ·
                    refine ⟨11407026141619212549834629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7604684094412808366556419 11407026141619212549834629)
                    ·
                      refine ⟨2138817401553602353093993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11407026141619212549834629 2138817401553602353093993)
                      ·
                        rfl

theorem cell23_4165332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4165332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165332 prefixEnd_4165332 := by exact prefixLift 4165332
  have htrace : WordTrace (prefixWord ++ tailWord_4165332) baseStart_4165332 baseEnd_4165332 := by
    simpa [prefixWord, tailWord_4165332, baseEnd_4165332] using wordTrace_append hprefix tailTrace_4165332
  have hstable : (prefixWord ++ tailWord_4165332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165332).length < 2 ^ (prefixWord ++ tailWord_4165332).sum := by decide
  have hdescent : baseEnd_4165332 < baseStart_4165332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165335 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 3]
def baseStart_4165335 : Nat := 118140960795 + 4165335 * 2 ^ 59
def prefixEnd_4165335 : Nat := 4983230072969 + 3 ^ 40 * 4165335 * 2
def baseEnd_4165335 : Nat := 2138818941995565841356479

theorem tailTrace_4165335 : CollatzResearch.WordTrace tailWord_4165335 prefixEnd_4165335 2138818941995565841356479 := by
  unfold tailWord_4165335
  simp only [CollatzResearch.WordTrace]
  refine ⟨151922248364710152427049459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101281498909806768284699639 151922248364710152427049459)
  ·
    refine ⟨227883372547065228640574189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151922248364710152427049459 227883372547065228640574189)
    ·
      refine ⟨85456264705149460740215321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227883372547065228640574189 85456264705149460740215321)
      ·
        refine ⟨64092198528862095555161491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85456264705149460740215321 64092198528862095555161491)
        ·
          refine ⟨96138297793293143332742237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64092198528862095555161491 96138297793293143332742237)
          ·
            refine ⟨36051861672484928749778339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96138297793293143332742237 36051861672484928749778339)
            ·
              refine ⟨54077792508727393124667509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36051861672484928749778339 54077792508727393124667509)
              ·
                refine ⟨5069793047693193105437579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54077792508727393124667509 5069793047693193105437579)
                ·
                  refine ⟨7604689571539789658156369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069793047693193105437579 7604689571539789658156369)
                  ·
                    refine ⟨5703517178654842243617277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7604689571539789658156369 5703517178654842243617277)
                    ·
                      refine ⟨2138818941995565841356479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5703517178654842243617277 2138818941995565841356479)
                      ·
                        rfl

theorem cell23_4165335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_4165335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165335 prefixEnd_4165335 := by exact prefixLift 4165335
  have htrace : WordTrace (prefixWord ++ tailWord_4165335) baseStart_4165335 baseEnd_4165335 := by
    simpa [prefixWord, tailWord_4165335, baseEnd_4165335] using wordTrace_append hprefix tailTrace_4165335
  have hstable : (prefixWord ++ tailWord_4165335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165335).length < 2 ^ (prefixWord ++ tailWord_4165335).sum := by decide
  have hdescent : baseEnd_4165335 < baseStart_4165335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165338 : List Nat := [3, 1, 1, 2, 2, 5, 9]
def baseStart_4165338 : Nat := 118140960795 + 4165338 * 2 ^ 59
def prefixEnd_4165338 : Nat := 4983230072969 + 3 ^ 40 * 4165338 * 2
def baseEnd_4165338 : Nat := 26405191141204065797765

theorem tailTrace_4165338 : CollatzResearch.WordTrace tailWord_4165338 prefixEnd_4165338 26405191141204065797765 := by
  unfold tailWord_4165338
  simp only [CollatzResearch.WordTrace]
  refine ⟨37980589445924820984852167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101281571855799522626272445 37980589445924820984852167)
  ·
    refine ⟨56970884168887231477278251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37980589445924820984852167 56970884168887231477278251)
    ·
      refine ⟨85456326253330847215917377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56970884168887231477278251 85456326253330847215917377)
      ·
        refine ⟨64092244689998135411938033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85456326253330847215917377 64092244689998135411938033)
        ·
          refine ⟨48069183517498601558953525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64092244689998135411938033 48069183517498601558953525)
          ·
            refine ⟨4506485954765493896151893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48069183517498601558953525 4506485954765493896151893)
            ·
              refine ⟨26405191141204065797765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4506485954765493896151893 26405191141204065797765)
              ·
                rfl

theorem cell23_4165338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 9].length) (baseStart_4165338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165338 prefixEnd_4165338 := by exact prefixLift 4165338
  have htrace : WordTrace (prefixWord ++ tailWord_4165338) baseStart_4165338 baseEnd_4165338 := by
    simpa [prefixWord, tailWord_4165338, baseEnd_4165338] using wordTrace_append hprefix tailTrace_4165338
  have hstable : (prefixWord ++ tailWord_4165338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165338).length < 2 ^ (prefixWord ++ tailWord_4165338).sum := by decide
  have hdescent : baseEnd_4165338 < baseStart_4165338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165358 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4165358 : Nat := 118140960795 + 4165358 * 2 ^ 59
def prefixEnd_4165358 : Nat := 4983230072969 + 3 ^ 40 * 4165358 * 2
def baseEnd_4165358 : Nat := 2138830752050619251368873

theorem tailTrace_4165358 : CollatzResearch.WordTrace tailWord_4165358 prefixEnd_4165358 2138830752050619251368873 := by
  unfold tailWord_4165358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18990385905453353419392091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101282058162417884903424485 18990385905453353419392091)
  ·
    refine ⟨28485578858180030129088137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18990385905453353419392091 28485578858180030129088137)
    ·
      refine ⟨21364184143635022596816103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28485578858180030129088137 21364184143635022596816103)
      ·
        refine ⟨32046276215452533895224155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21364184143635022596816103 32046276215452533895224155)
        ·
          refine ⟨48069414323178800842836233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32046276215452533895224155 48069414323178800842836233)
          ·
            refine ⟨36052060742384100632127175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48069414323178800842836233 36052060742384100632127175)
            ·
              refine ⟨54078091113576150948190763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36052060742384100632127175 54078091113576150948190763)
              ·
                refine ⟨81117136670364226422286145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54078091113576150948190763 81117136670364226422286145)
                ·
                  refine ⟨60837852502773169816714609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81117136670364226422286145 60837852502773169816714609)
                  ·
                    refine ⟨45628389377079877362535957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60837852502773169816714609 45628389377079877362535957)
                    ·
                      refine ⟨2138830752050619251368873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45628389377079877362535957 2138830752050619251368873)
                      ·
                        rfl

theorem cell23_4165358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4165358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165358 prefixEnd_4165358 := by exact prefixLift 4165358
  have htrace : WordTrace (prefixWord ++ tailWord_4165358) baseStart_4165358 baseEnd_4165358 := by
    simpa [prefixWord, tailWord_4165358, baseEnd_4165358] using wordTrace_append hprefix tailTrace_4165358
  have hstable : (prefixWord ++ tailWord_4165358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165358).length < 2 ^ (prefixWord ++ tailWord_4165358).sum := by decide
  have hdescent : baseEnd_4165358 < baseStart_4165358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165389 : List Nat := [1, 7, 2, 1, 1, 11]
def baseStart_4165389 : Nat := 118140960795 + 4165389 * 2 ^ 59
def prefixEnd_4165389 : Nat := 4983230072969 + 3 ^ 40 * 4165389 * 2
def baseEnd_4165389 : Nat := 8801838147946126049717

theorem tailTrace_4165389 : CollatzResearch.WordTrace tailWord_4165389 prefixEnd_4165389 8801838147946126049717 := by
  unfold tailWord_4165389
  simp only [CollatzResearch.WordTrace]
  refine ⟨151924217906514519649515221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101282811937676346433010147 151924217906514519649515221)
  ·
    refine ⟨3560723857183934054285513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 151924217906514519649515221 3560723857183934054285513)
    ·
      refine ⟨2670542892887950540714135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3560723857183934054285513 2670542892887950540714135)
      ·
        refine ⟨4005814339331925811071203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670542892887950540714135 4005814339331925811071203)
        ·
          refine ⟨6008721508997888716606805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005814339331925811071203 6008721508997888716606805)
          ·
            refine ⟨8801838147946126049717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6008721508997888716606805 8801838147946126049717)
            ·
              rfl

theorem cell23_4165389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 11].length) (baseStart_4165389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165389 prefixEnd_4165389 := by exact prefixLift 4165389
  have htrace : WordTrace (prefixWord ++ tailWord_4165389) baseStart_4165389 baseEnd_4165389 := by
    simpa [prefixWord, tailWord_4165389, baseEnd_4165389] using wordTrace_append hprefix tailTrace_4165389
  have hstable : (prefixWord ++ tailWord_4165389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165389).length < 2 ^ (prefixWord ++ tailWord_4165389).sum := by decide
  have hdescent : baseEnd_4165389 < baseStart_4165389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165399 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 3]
def baseStart_4165399 : Nat := 118140960795 + 4165399 * 2 ^ 59
def prefixEnd_4165399 : Nat := 4983230072969 + 3 ^ 40 * 4165399 * 2
def baseEnd_4165399 : Nat := 2138851804757453590956185

theorem tailTrace_4165399 : CollatzResearch.WordTrace tailWord_4165399 prefixEnd_4165399 2138851804757453590956185 := by
  unfold tailWord_4165399
  simp only [CollatzResearch.WordTrace]
  refine ⟨151924582636478291357379251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101283055090985527571586167 151924582636478291357379251)
  ·
    refine ⟨227886873954717437036068877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151924582636478291357379251 227886873954717437036068877)
    ·
      refine ⟨85457577733019038888525829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227886873954717437036068877 85457577733019038888525829)
      ·
        refine ⟨16023295824941069791598593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85457577733019038888525829 16023295824941069791598593)
        ·
          refine ⟨12017471868705802343698945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16023295824941069791598593 12017471868705802343698945)
          ·
            refine ⟨9013103901529351757774209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12017471868705802343698945 9013103901529351757774209)
            ·
              refine ⟨6759827926147013818330657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9013103901529351757774209 6759827926147013818330657)
              ·
                refine ⟨5069870944610260363747993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6759827926147013818330657 5069870944610260363747993)
                ·
                  refine ⟨3802403208457695272810995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5069870944610260363747993 3802403208457695272810995)
                  ·
                    refine ⟨5703604812686542909216493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3802403208457695272810995 5703604812686542909216493)
                    ·
                      refine ⟨2138851804757453590956185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5703604812686542909216493 2138851804757453590956185)
                      ·
                        rfl

theorem cell23_4165399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_4165399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165399 prefixEnd_4165399 := by exact prefixLift 4165399
  have htrace : WordTrace (prefixWord ++ tailWord_4165399) baseStart_4165399 baseEnd_4165399 := by
    simpa [prefixWord, tailWord_4165399, baseEnd_4165399] using wordTrace_append hprefix tailTrace_4165399
  have hstable : (prefixWord ++ tailWord_4165399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165399).length < 2 ^ (prefixWord ++ tailWord_4165399).sum := by decide
  have hdescent : baseEnd_4165399 < baseStart_4165399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165406 : List Nat := [4, 3, 2, 2, 2, 1, 1, 8]
def baseStart_4165406 : Nat := 118140960795 + 4165406 * 2 ^ 59
def prefixEnd_4165406 : Nat := 4983230072969 + 3 ^ 40 * 4165406 * 2
def baseEnd_4165406 : Nat := 79216866634149446798839

theorem tailTrace_4165406 : CollatzResearch.WordTrace tailWord_4165406 prefixEnd_4165406 79216866634149446798839 := by
  unfold tailWord_4165406
  simp only [CollatzResearch.WordTrace]
  refine ⟨18990604743431616444110509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101283225298301954368589381 18990604743431616444110509)
  ·
    refine ⟨7121476778786856166541441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18990604743431616444110509 7121476778786856166541441)
    ·
      refine ⟨5341107584090142124906081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7121476778786856166541441 5341107584090142124906081)
      ·
        refine ⟨4005830688067606593679561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5341107584090142124906081 4005830688067606593679561)
        ·
          refine ⟨3004373016050704945259671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4005830688067606593679561 3004373016050704945259671)
          ·
            refine ⟨4506559524076057417889507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004373016050704945259671 4506559524076057417889507)
            ·
              refine ⟨6759839286114086126834261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506559524076057417889507 6759839286114086126834261)
              ·
                refine ⟨79216866634149446798839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6759839286114086126834261 79216866634149446798839)
                ·
                  rfl

theorem cell23_4165406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_4165406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165406 prefixEnd_4165406 := by exact prefixLift 4165406
  have htrace : WordTrace (prefixWord ++ tailWord_4165406) baseStart_4165406 baseEnd_4165406 := by
    simpa [prefixWord, tailWord_4165406, baseEnd_4165406] using wordTrace_append hprefix tailTrace_4165406
  have hstable : (prefixWord ++ tailWord_4165406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165406).length < 2 ^ (prefixWord ++ tailWord_4165406).sum := by decide
  have hdescent : baseEnd_4165406 < baseStart_4165406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165488 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 1, 10]
def baseStart_4165488 : Nat := 118140960795 + 4165488 * 2 ^ 59
def prefixEnd_4165488 : Nat := 4983230072969 + 3 ^ 40 * 4165488 * 2
def baseEnd_4165488 : Nat := 712965834845234580914425

theorem tailTrace_4165488 : CollatzResearch.WordTrace tailWord_4165488 prefixEnd_4165488 712965834845234580914425 := by
  unfold tailWord_4165488
  simp only [CollatzResearch.WordTrace]
  refine ⟨75963914366577929778684559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101285219155437239704912745 75963914366577929778684559)
  ·
    refine ⟨113945871549866894668026839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75963914366577929778684559 113945871549866894668026839)
    ·
      refine ⟨170918807324800342002040259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113945871549866894668026839 170918807324800342002040259)
      ·
        refine ⟨256378210987200513003060389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170918807324800342002040259 256378210987200513003060389)
        ·
          refine ⟨48070914560100096188073823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256378210987200513003060389 48070914560100096188073823)
          ·
            refine ⟨72106371840150144282110735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48070914560100096188073823 72106371840150144282110735)
            ·
              refine ⟨108159557760225216423166103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72106371840150144282110735 108159557760225216423166103)
              ·
                refine ⟨162239336640337824634749155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108159557760225216423166103 162239336640337824634749155)
                ·
                  refine ⟨243359004960506736952123733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162239336640337824634749155 243359004960506736952123733)
                  ·
                    refine ⟨712965834845234580914425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 243359004960506736952123733 712965834845234580914425)
                    ·
                      rfl

theorem cell23_4165488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_4165488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165488 prefixEnd_4165488 := by exact prefixLift 4165488
  have htrace : WordTrace (prefixWord ++ tailWord_4165488) baseStart_4165488 baseEnd_4165488 := by
    simpa [prefixWord, tailWord_4165488, baseEnd_4165488] using wordTrace_append hprefix tailTrace_4165488
  have hstable : (prefixWord ++ tailWord_4165488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165488).length < 2 ^ (prefixWord ++ tailWord_4165488).sum := by decide
  have hdescent : baseEnd_4165488 < baseStart_4165488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165562 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3]
def baseStart_4165562 : Nat := 118140960795 + 4165562 * 2 ^ 59
def prefixEnd_4165562 : Nat := 4983230072969 + 3 ^ 40 * 4165562 * 2
def baseEnd_4165562 : Nat := 2138935502104136453217935

theorem tailTrace_4165562 : CollatzResearch.WordTrace tailWord_4165562 prefixEnd_4165562 2138935502104136453217935 := by
  unfold tailWord_4165562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37982631933721942548890735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101287018489925180130375293 37982631933721942548890735)
  ·
    refine ⟨56973947900582913823336103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37982631933721942548890735 56973947900582913823336103)
    ·
      refine ⟨85460921850874370735004155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56973947900582913823336103 85460921850874370735004155)
      ·
        refine ⟨128191382776311556102506233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85460921850874370735004155 128191382776311556102506233)
        ·
          refine ⟨96143537082233667076879675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128191382776311556102506233 96143537082233667076879675)
          ·
            refine ⟨144215305623350500615319513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96143537082233667076879675 144215305623350500615319513)
            ·
              refine ⟨108161479217512875461489635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144215305623350500615319513 108161479217512875461489635)
              ·
                refine ⟨162242218826269313192234453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108161479217512875461489635 162242218826269313192234453)
                ·
                  refine ⟨3802552003740687027942995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 162242218826269313192234453 3802552003740687027942995)
                  ·
                    refine ⟨5703828005611030541914493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3802552003740687027942995 5703828005611030541914493)
                    ·
                      refine ⟨2138935502104136453217935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5703828005611030541914493 2138935502104136453217935)
                      ·
                        rfl

theorem cell23_4165562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_4165562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165562 prefixEnd_4165562 := by exact prefixLift 4165562
  have htrace : WordTrace (prefixWord ++ tailWord_4165562) baseStart_4165562 baseEnd_4165562 := by
    simpa [prefixWord, tailWord_4165562, baseEnd_4165562] using wordTrace_append hprefix tailTrace_4165562
  have hstable : (prefixWord ++ tailWord_4165562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165562).length < 2 ^ (prefixWord ++ tailWord_4165562).sum := by decide
  have hdescent : baseEnd_4165562 < baseStart_4165562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165625 : List Nat := [1, 2, 1, 3, 1, 5, 10]
def baseStart_4165625 : Nat := 118140960795 + 4165625 * 2 ^ 59
def prefixEnd_4165625 : Nat := 4983230072969 + 3 ^ 40 * 4165625 * 2
def baseEnd_4165625 : Nat := 26407010510930490206545

theorem tailTrace_4165625 : CollatzResearch.WordTrace tailWord_4165625 prefixEnd_4165625 26407010510930490206545 := by
  unfold tailWord_4165625
  simp only [CollatzResearch.WordTrace]
  refine ⟨151932825533659531955106329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101288550355773021303404219 151932825533659531955106329)
  ·
    refine ⟨113949619150244648966329747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151932825533659531955106329 113949619150244648966329747)
    ·
      refine ⟨170924428725366973449494621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113949619150244648966329747 170924428725366973449494621)
      ·
        refine ⟨64096660772012615043560483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170924428725366973449494621 64096660772012615043560483)
        ·
          refine ⟨96144991158018922565340725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64096660772012615043560483 96144991158018922565340725)
          ·
            refine ⟨9013592921064273990500693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96144991158018922565340725 9013592921064273990500693)
            ·
              refine ⟨26407010510930490206545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9013592921064273990500693 26407010510930490206545)
              ·
                rfl

theorem cell23_4165625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 10].length) (baseStart_4165625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165625 prefixEnd_4165625 := by exact prefixLift 4165625
  have htrace : WordTrace (prefixWord ++ tailWord_4165625) baseStart_4165625 baseEnd_4165625 := by
    simpa [prefixWord, tailWord_4165625, baseEnd_4165625] using wordTrace_append hprefix tailTrace_4165625
  have hstable : (prefixWord ++ tailWord_4165625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165625).length < 2 ^ (prefixWord ++ tailWord_4165625).sum := by decide
  have hdescent : baseEnd_4165625 < baseStart_4165625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165629 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_4165629 : Nat := 118140960795 + 4165629 * 2 ^ 59
def prefixEnd_4165629 : Nat := 4983230072969 + 3 ^ 40 * 4165629 * 2
def baseEnd_4165629 : Nat := 712989968435995897026709

theorem tailTrace_4165629 : CollatzResearch.WordTrace tailWord_4165629 prefixEnd_4165629 712989968435995897026709 := by
  unfold tailWord_4165629
  simp only [CollatzResearch.WordTrace]
  refine ⟨151932971425645040638251941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101288647617096693758834627 151932971425645040638251941)
  ·
    refine ⟨28487432142308445119672239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151932971425645040638251941 28487432142308445119672239)
    ·
      refine ⟨42731148213462667679508359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28487432142308445119672239 42731148213462667679508359)
      ·
        refine ⟨64096722320194001519262539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42731148213462667679508359 64096722320194001519262539)
        ·
          refine ⟨96145083480291002278893809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64096722320194001519262539 96145083480291002278893809)
          ·
            refine ⟨72108812610218251709170357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96145083480291002278893809 72108812610218251709170357)
            ·
              refine ⟨6760201182207961097734721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72108812610218251709170357 6760201182207961097734721)
              ·
                refine ⟨5070150886655970823301041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6760201182207961097734721 5070150886655970823301041)
                ·
                  refine ⟨3802613164991978117475781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5070150886655970823301041 3802613164991978117475781)
                  ·
                    refine ⟨712989968435995897026709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3802613164991978117475781 712989968435995897026709)
                    ·
                      rfl

theorem cell23_4165629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_4165629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165629 prefixEnd_4165629 := by exact prefixLift 4165629
  have htrace : WordTrace (prefixWord ++ tailWord_4165629) baseStart_4165629 baseEnd_4165629 := by
    simpa [prefixWord, tailWord_4165629, baseEnd_4165629] using wordTrace_append hprefix tailTrace_4165629
  have hstable : (prefixWord ++ tailWord_4165629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165629).length < 2 ^ (prefixWord ++ tailWord_4165629).sum := by decide
  have hdescent : baseEnd_4165629 < baseStart_4165629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165646 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_4165646 : Nat := 118140960795 + 4165646 * 2 ^ 59
def prefixEnd_4165646 : Nat := 4983230072969 + 3 ^ 40 * 4165646 * 2
def baseEnd_4165646 : Nat := 712992878159704708189183

theorem tailTrace_4165646 : CollatzResearch.WordTrace tailWord_4165646 prefixEnd_4165646 712992878159704708189183 := by
  unfold tailWord_4165646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18991698933322931567702599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101289060977722301694413861 18991698933322931567702599)
  ·
    refine ⟨28487548399984397351553899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18991698933322931567702599 28487548399984397351553899)
    ·
      refine ⟨42731322599976596027330849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28487548399984397351553899 42731322599976596027330849)
      ·
        refine ⟨32048491949982447020498137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42731322599976596027330849 32048491949982447020498137)
        ·
          refine ⟨24036368962486835265373603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32048491949982447020498137 24036368962486835265373603)
          ·
            refine ⟨36054553443730252898060405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24036368962486835265373603 36054553443730252898060405)
            ·
              refine ⟨3380114385349711209193163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36054553443730252898060405 3380114385349711209193163)
              ·
                refine ⟨5070171578024566813789745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380114385349711209193163 5070171578024566813789745)
                ·
                  refine ⟨3802628683518425110342309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5070171578024566813789745 3802628683518425110342309)
                  ·
                    refine ⟨712992878159704708189183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3802628683518425110342309 712992878159704708189183)
                    ·
                      rfl

theorem cell23_4165646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_4165646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165646 prefixEnd_4165646 := by exact prefixLift 4165646
  have htrace : WordTrace (prefixWord ++ tailWord_4165646) baseStart_4165646 baseEnd_4165646 := by
    simpa [prefixWord, tailWord_4165646, baseEnd_4165646] using wordTrace_append hprefix tailTrace_4165646
  have hstable : (prefixWord ++ tailWord_4165646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165646).length < 2 ^ (prefixWord ++ tailWord_4165646).sum := by decide
  have hdescent : baseEnd_4165646 < baseStart_4165646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165669 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 3]
def baseStart_4165669 : Nat := 118140960795 + 4165669 * 2 ^ 59
def prefixEnd_4165669 : Nat := 4983230072969 + 3 ^ 40 * 4165669 * 2
def baseEnd_4165669 : Nat := 2138990444534167534579943

theorem tailTrace_4165669 : CollatzResearch.WordTrace tailWord_4165669 prefixEnd_4165669 2138990444534167534579943 := by
  unfold tailWord_4165669
  simp only [CollatzResearch.WordTrace]
  refine ⟨151934430345500127469708061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101289620230333418313138707 151934430345500127469708061)
  ·
    refine ⟨56975411379562547801140523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151934430345500127469708061 56975411379562547801140523)
    ·
      refine ⟨85463117069343821701710785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56975411379562547801140523 85463117069343821701710785)
      ·
        refine ⟨64097337802007866276283089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85463117069343821701710785 64097337802007866276283089)
        ·
          refine ⟨48073003351505899707212317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64097337802007866276283089 48073003351505899707212317)
          ·
            refine ⟨18027376256814712390204619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48073003351505899707212317 18027376256814712390204619)
            ·
              refine ⟨27041064385222068585306929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18027376256814712390204619 27041064385222068585306929)
              ·
                refine ⟨20280798288916551438980197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27041064385222068585306929 20280798288916551438980197)
                ·
                  refine ⟨3802649679171853394808787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20280798288916551438980197 3802649679171853394808787)
                  ·
                    refine ⟨5703974518757780092213181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3802649679171853394808787 5703974518757780092213181)
                    ·
                      refine ⟨2138990444534167534579943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5703974518757780092213181 2138990444534167534579943)
                      ·
                        rfl

theorem cell23_4165669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_4165669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165669 prefixEnd_4165669 := by exact prefixLift 4165669
  have htrace : WordTrace (prefixWord ++ tailWord_4165669) baseStart_4165669 baseEnd_4165669 := by
    simpa [prefixWord, tailWord_4165669, baseEnd_4165669] using wordTrace_append hprefix tailTrace_4165669
  have hstable : (prefixWord ++ tailWord_4165669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165669).length < 2 ^ (prefixWord ++ tailWord_4165669).sum := by decide
  have hdescent : baseEnd_4165669 < baseStart_4165669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165686 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_4165686 : Nat := 118140960795 + 4165686 * 2 ^ 59
def prefixEnd_4165686 : Nat := 4983230072969 + 3 ^ 40 * 4165686 * 2
def baseEnd_4165686 : Nat := 2138999173705293968067365

theorem tailTrace_4165686 : CollatzResearch.WordTrace tailWord_4165686 prefixEnd_4165686 2138999173705293968067365 := by
  unfold tailWord_4165686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495940649152408710817307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101290033590959026248717941 9495940649152408710817307)
  ·
    refine ⟨14243910973728613066225961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9495940649152408710817307 14243910973728613066225961)
    ·
      refine ⟨10682933230296459799669471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14243910973728613066225961 10682933230296459799669471)
      ·
        refine ⟨16024399845444689699504207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10682933230296459799669471 16024399845444689699504207)
        ·
          refine ⟨24036599768167034549256311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16024399845444689699504207 24036599768167034549256311)
          ·
            refine ⟨36054899652250551823884467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24036599768167034549256311 36054899652250551823884467)
            ·
              refine ⟨54082349478375827735826701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36054899652250551823884467 54082349478375827735826701)
              ·
                refine ⟨20280881054390935400935013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54082349478375827735826701 20280881054390935400935013)
                ·
                  refine ⟨3802665197698300387675315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20280881054390935400935013 3802665197698300387675315)
                  ·
                    refine ⟨5703997796547450581512973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3802665197698300387675315 5703997796547450581512973)
                    ·
                      refine ⟨2138999173705293968067365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5703997796547450581512973 2138999173705293968067365)
                      ·
                        rfl

theorem cell23_4165686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_4165686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165686 prefixEnd_4165686 := by exact prefixLift 4165686
  have htrace : WordTrace (prefixWord ++ tailWord_4165686) baseStart_4165686 baseEnd_4165686 := by
    simpa [prefixWord, tailWord_4165686, baseEnd_4165686] using wordTrace_append hprefix tailTrace_4165686
  have hstable : (prefixWord ++ tailWord_4165686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165686).length < 2 ^ (prefixWord ++ tailWord_4165686).sum := by decide
  have hdescent : baseEnd_4165686 < baseStart_4165686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165692 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_4165692 : Nat := 118140960795 + 4165692 * 2 ^ 59
def prefixEnd_4165692 : Nat := 4983230072969 + 3 ^ 40 * 4165692 * 2
def baseEnd_4165692 : Nat := 2139002254589220944592337

theorem tailTrace_4165692 : CollatzResearch.WordTrace tailWord_4165692 prefixEnd_4165692 2139002254589220944592337 := by
  unfold tailWord_4165692
  simp only [CollatzResearch.WordTrace]
  refine ⟨75967634612208401198897665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101290179482944534931863553 75967634612208401198897665)
  ·
    refine ⟨56975725959156300899173249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75967634612208401198897665 56975725959156300899173249)
    ·
      refine ⟨42731794469367225674379937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56975725959156300899173249 42731794469367225674379937)
      ·
        refine ⟨32048845852025419255784953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42731794469367225674379937 32048845852025419255784953)
        ·
          refine ⟨24036634389019064441838715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32048845852025419255784953 24036634389019064441838715)
          ·
            refine ⟨36054951583528596662758073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24036634389019064441838715 36054951583528596662758073)
            ·
              refine ⟨27041213687646447497068555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36054951583528596662758073 27041213687646447497068555)
              ·
                refine ⟨40561820531469671245602833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27041213687646447497068555 40561820531469671245602833)
                ·
                  refine ⟨30421365398602253434202125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40561820531469671245602833 30421365398602253434202125)
                  ·
                    refine ⟨11408012024475845037825797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30421365398602253434202125 11408012024475845037825797)
                    ·
                      refine ⟨2139002254589220944592337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11408012024475845037825797 2139002254589220944592337)
                      ·
                        rfl

theorem cell23_4165692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_4165692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165692 prefixEnd_4165692 := by exact prefixLift 4165692
  have htrace : WordTrace (prefixWord ++ tailWord_4165692) baseStart_4165692 baseEnd_4165692 := by
    simpa [prefixWord, tailWord_4165692, baseEnd_4165692] using wordTrace_append hprefix tailTrace_4165692
  have hstable : (prefixWord ++ tailWord_4165692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165692).length < 2 ^ (prefixWord ++ tailWord_4165692).sum := by decide
  have hdescent : baseEnd_4165692 < baseStart_4165692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165743 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 2, 2, 2]
def baseStart_4165743 : Nat := 118140960795 + 4165743 * 2 ^ 59
def prefixEnd_4165743 : Nat := 4983230072969 + 3 ^ 40 * 4165743 * 2
def baseEnd_4165743 : Nat := 2139028442102600245054603

theorem tailTrace_4165743 : CollatzResearch.WordTrace tailWord_4165743 prefixEnd_4165743 2139028442102600245054603 := by
  unfold tailWord_4165743
  simp only [CollatzResearch.WordTrace]
  refine ⟨151937129347232038107901883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101291419564821358738601255 151937129347232038107901883)
  ·
    refine ⟨227905694020848057161852825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151937129347232038107901883 227905694020848057161852825)
    ·
      refine ⟨170929270515636042871389619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227905694020848057161852825 170929270515636042871389619)
      ·
        refine ⟨256393905773454064307084429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170929270515636042871389619 256393905773454064307084429)
        ·
          refine ⟨96147714665045274115156661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256393905773454064307084429 96147714665045274115156661)
          ·
            refine ⟨9013848249847994448295937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96147714665045274115156661 9013848249847994448295937)
            ·
              refine ⟨6760386187385995836221953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9013848249847994448295937 6760386187385995836221953)
              ·
                refine ⟨5070289640539496877166465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6760386187385995836221953 5070289640539496877166465)
                ·
                  refine ⟨3802717230404622657874849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5070289640539496877166465 3802717230404622657874849)
                  ·
                    refine ⟨2852037922803466993406137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3802717230404622657874849 2852037922803466993406137)
                    ·
                      refine ⟨2139028442102600245054603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852037922803466993406137 2139028442102600245054603)
                      ·
                        rfl

theorem cell23_4165743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 2, 2].length) (baseStart_4165743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165743 prefixEnd_4165743 := by exact prefixLift 4165743
  have htrace : WordTrace (prefixWord ++ tailWord_4165743) baseStart_4165743 baseEnd_4165743 := by
    simpa [prefixWord, tailWord_4165743, baseEnd_4165743] using wordTrace_append hprefix tailTrace_4165743
  have hstable : (prefixWord ++ tailWord_4165743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165743).length < 2 ^ (prefixWord ++ tailWord_4165743).sum := by decide
  have hdescent : baseEnd_4165743 < baseStart_4165743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165769 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 2, 5, 2]
def baseStart_4165769 : Nat := 118140960795 + 4165769 * 2 ^ 59
def prefixEnd_4165769 : Nat := 4983230072969 + 3 ^ 40 * 4165769 * 2
def baseEnd_4165769 : Nat := 2139041792599617143329483

theorem tailTrace_4165769 : CollatzResearch.WordTrace tailWord_4165769 prefixEnd_4165769 2139041792599617143329483 := by
  unfold tailWord_4165769
  simp only [CollatzResearch.WordTrace]
  refine ⟨151938077645137844548348361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101292051763425229698898907 151938077645137844548348361)
  ·
    refine ⟨113953558233853383411261271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151938077645137844548348361 113953558233853383411261271)
    ·
      refine ⟨170930337350780075116891907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113953558233853383411261271 170930337350780075116891907)
      ·
        refine ⟨256395506026170112675337861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170930337350780075116891907 256395506026170112675337861)
        ·
          refine ⟨48074157379906896126625849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256395506026170112675337861 48074157379906896126625849)
          ·
            refine ⟨36055618034930172094969387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48074157379906896126625849 36055618034930172094969387)
            ·
              refine ⟨54083427052395258142454081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36055618034930172094969387 54083427052395258142454081)
              ·
                refine ⟨40562570289296443606840561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54083427052395258142454081 40562570289296443606840561)
                ·
                  refine ⟨30421927716972332705130421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40562570289296443606840561 30421927716972332705130421)
                  ·
                    refine ⟨2852055723466156191105977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30421927716972332705130421 2852055723466156191105977)
                    ·
                      refine ⟨2139041792599617143329483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852055723466156191105977 2139041792599617143329483)
                      ·
                        rfl

theorem cell23_4165769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 5, 2].length) (baseStart_4165769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165769 prefixEnd_4165769 := by exact prefixLift 4165769
  have htrace : WordTrace (prefixWord ++ tailWord_4165769) baseStart_4165769 baseEnd_4165769 := by
    simpa [prefixWord, tailWord_4165769, baseEnd_4165769] using wordTrace_append hprefix tailTrace_4165769
  have hstable : (prefixWord ++ tailWord_4165769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165769).length < 2 ^ (prefixWord ++ tailWord_4165769).sum := by decide
  have hdescent : baseEnd_4165769 < baseStart_4165769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165853 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_4165853 : Nat := 118140960795 + 4165853 * 2 ^ 59
def prefixEnd_4165853 : Nat := 4983230072969 + 3 ^ 40 * 4165853 * 2
def baseEnd_4165853 : Nat := 2139084924974594814679097

theorem tailTrace_4165853 : CollatzResearch.WordTrace tailWord_4165853 prefixEnd_4165853 2139084924974594814679097 := by
  unfold tailWord_4165853
  simp only [CollatzResearch.WordTrace]
  refine ⟨151941141376833526894406213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101294094251222351262937475 151941141376833526894406213)
  ·
    refine ⟨28488964008156286292701165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151941141376833526894406213 28488964008156286292701165)
    ·
      refine ⟨10683361503058607359762937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28488964008156286292701165 10683361503058607359762937)
      ·
        refine ⟨8012521127293955519822203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10683361503058607359762937 8012521127293955519822203)
        ·
          refine ⟨12018781690940933279733305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8012521127293955519822203 12018781690940933279733305)
          ·
            refine ⟨9014086268205699959799979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12018781690940933279733305 9014086268205699959799979)
            ·
              refine ⟨13521129402308549939699969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014086268205699959799979 13521129402308549939699969)
              ·
                refine ⟨10140847051731412454774977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13521129402308549939699969 10140847051731412454774977)
                ·
                  refine ⟨7605635288798559341081233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10140847051731412454774977 7605635288798559341081233)
                  ·
                    refine ⟨5704226466598919505810925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7605635288798559341081233 5704226466598919505810925)
                    ·
                      refine ⟨2139084924974594814679097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5704226466598919505810925 2139084924974594814679097)
                      ·
                        rfl

theorem cell23_4165853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_4165853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165853 prefixEnd_4165853 := by exact prefixLift 4165853
  have htrace : WordTrace (prefixWord ++ tailWord_4165853) baseStart_4165853 baseEnd_4165853 := by
    simpa [prefixWord, tailWord_4165853, baseEnd_4165853] using wordTrace_append hprefix tailTrace_4165853
  have hstable : (prefixWord ++ tailWord_4165853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165853).length < 2 ^ (prefixWord ++ tailWord_4165853).sum := by decide
  have hdescent : baseEnd_4165853 < baseStart_4165853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165886 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_4165886 : Nat := 118140960795 + 4165886 * 2 ^ 59
def prefixEnd_4165886 : Nat := 4983230072969 + 3 ^ 40 * 4165886 * 2
def baseEnd_4165886 : Nat := 713033956612064395188815

theorem tailTrace_4165886 : CollatzResearch.WordTrace tailWord_4165886 prefixEnd_4165886 713033956612064395188815 := by
  unfold tailWord_4165886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18992793123214246691294689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101294896657142649020238341 18992793123214246691294689)
  ·
    refine ⟨14244594842410685018471017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18992793123214246691294689 14244594842410685018471017)
    ·
      refine ⟨10683446131808013763853263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14244594842410685018471017 10683446131808013763853263)
      ·
        refine ⟨16025169197712020645779895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683446131808013763853263 16025169197712020645779895)
        ·
          refine ⟨24037753796568030968669843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16025169197712020645779895 24037753796568030968669843)
          ·
            refine ⟨36056630694852046453004765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24037753796568030968669843 36056630694852046453004765)
            ·
              refine ⟨13521236510569517419876787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36056630694852046453004765 13521236510569517419876787)
              ·
                refine ⟨20281854765854276129815181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13521236510569517419876787 20281854765854276129815181)
                ·
                  refine ⟨7605695537195353548680693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20281854765854276129815181 7605695537195353548680693)
                  ·
                    refine ⟨713033956612064395188815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7605695537195353548680693 713033956612064395188815)
                    ·
                      rfl

theorem cell23_4165886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_4165886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165886 prefixEnd_4165886 := by exact prefixLift 4165886
  have htrace : WordTrace (prefixWord ++ tailWord_4165886) baseStart_4165886 baseEnd_4165886 := by
    simpa [prefixWord, tailWord_4165886, baseEnd_4165886] using wordTrace_append hprefix tailTrace_4165886
  have hstable : (prefixWord ++ tailWord_4165886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165886).length < 2 ^ (prefixWord ++ tailWord_4165886).sum := by decide
  have hdescent : baseEnd_4165886 < baseStart_4165886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165899 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 1, 6]
def baseStart_4165899 : Nat := 118140960795 + 4165899 * 2 ^ 59
def prefixEnd_4165899 : Nat := 4983230072969 + 3 ^ 40 * 4165899 * 2
def baseEnd_4165899 : Nat := 713036181694900544901295

theorem tailTrace_4165899 : CollatzResearch.WordTrace tailWord_4165899 prefixEnd_4165899 713036181694900544901295 := by
  unfold tailWord_4165899
  simp only [CollatzResearch.WordTrace]
  refine ⟨151942819134666876750580751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101295212756444584500387167 151942819134666876750580751)
  ·
    refine ⟨227914228702000315125871127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151942819134666876750580751 227914228702000315125871127)
    ·
      refine ⟨341871343053000472688806691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227914228702000315125871127 341871343053000472688806691)
      ·
        refine ⟨512807014579500709033210037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341871343053000472688806691 512807014579500709033210037)
        ·
          refine ⟨48075657616828191471863441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 512807014579500709033210037 48075657616828191471863441)
          ·
            refine ⟨36056743212621143603897581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48075657616828191471863441 36056743212621143603897581)
            ·
              refine ⟨13521278704732928851461593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36056743212621143603897581 13521278704732928851461593)
              ·
                refine ⟨10140959028549696638596195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13521278704732928851461593 10140959028549696638596195)
                ·
                  refine ⟨15211438542824544957894293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10140959028549696638596195 15211438542824544957894293)
                  ·
                    refine ⟨713036181694900544901295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15211438542824544957894293 713036181694900544901295)
                    ·
                      rfl

theorem cell23_4165899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 6].length) (baseStart_4165899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165899 prefixEnd_4165899 := by exact prefixLift 4165899
  have htrace : WordTrace (prefixWord ++ tailWord_4165899) baseStart_4165899 baseEnd_4165899 := by
    simpa [prefixWord, tailWord_4165899, baseEnd_4165899] using wordTrace_append hprefix tailTrace_4165899
  have hstable : (prefixWord ++ tailWord_4165899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165899).length < 2 ^ (prefixWord ++ tailWord_4165899).sum := by decide
  have hdescent : baseEnd_4165899 < baseStart_4165899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165917 : List Nat := [1, 4, 2, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_4165917 : Nat := 118140960795 + 4165917 * 2 ^ 59
def prefixEnd_4165917 : Nat := 4983230072969 + 3 ^ 40 * 4165917 * 2
def baseEnd_4165917 : Nat := 2139117787736482564278803

theorem tailTrace_4165917 : CollatzResearch.WordTrace tailWord_4165917 prefixEnd_4165917 2139117787736482564278803 := by
  unfold tailWord_4165917
  simp only [CollatzResearch.WordTrace]
  refine ⟨151943475648601665824736005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101295650432401110549824003 151943475648601665824736005)
  ·
    refine ⟨28489401684112812342138001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151943475648601665824736005 28489401684112812342138001)
    ·
      refine ⟨21367051263084609256603501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28489401684112812342138001 21367051263084609256603501)
      ·
        refine ⟨8012644223656728471226313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21367051263084609256603501 8012644223656728471226313)
        ·
          refine ⟨6009483167742546353419735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8012644223656728471226313 6009483167742546353419735)
          ·
            refine ⟨9014224751613819530129603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009483167742546353419735 9014224751613819530129603)
            ·
              refine ⟨13521337127420729295194405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014224751613819530129603 13521337127420729295194405)
              ·
                refine ⟨2535250711391386742848951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13521337127420729295194405 2535250711391386742848951)
                ·
                  refine ⟨3802876067087080114273427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535250711391386742848951 3802876067087080114273427)
                  ·
                    refine ⟨5704314100630620171410141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3802876067087080114273427 5704314100630620171410141)
                    ·
                      refine ⟨2139117787736482564278803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5704314100630620171410141 2139117787736482564278803)
                      ·
                        rfl

theorem cell23_4165917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_4165917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165917 prefixEnd_4165917 := by exact prefixLift 4165917
  have htrace : WordTrace (prefixWord ++ tailWord_4165917) baseStart_4165917 baseEnd_4165917 := by
    simpa [prefixWord, tailWord_4165917, baseEnd_4165917] using wordTrace_append hprefix tailTrace_4165917
  have hstable : (prefixWord ++ tailWord_4165917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165917).length < 2 ^ (prefixWord ++ tailWord_4165917).sum := by decide
  have hdescent : baseEnd_4165917 < baseStart_4165917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165923 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 3, 2, 2]
def baseStart_4165923 : Nat := 118140960795 + 4165923 * 2 ^ 59
def prefixEnd_4165923 : Nat := 4983230072969 + 3 ^ 40 * 4165923 * 2
def baseEnd_4165923 : Nat := 2139120868620409540803775

theorem tailTrace_4165923 : CollatzResearch.WordTrace tailWord_4165923 prefixEnd_4165923 2139120868620409540803775 := by
  unfold tailWord_4165923
  simp only [CollatzResearch.WordTrace]
  refine ⟨151943694486579928849454423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101295796324386619232969615 151943694486579928849454423)
  ·
    refine ⟨227915541729869893274181635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151943694486579928849454423 227915541729869893274181635)
    ·
      refine ⟨341873312594804839911272453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227915541729869893274181635 341873312594804839911272453)
      ·
        refine ⟨64101246111525907483363585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341873312594804839911272453 64101246111525907483363585)
        ·
          refine ⟨48075934583644430612522689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64101246111525907483363585 48075934583644430612522689)
          ·
            refine ⟨36056950937733322959392017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48075934583644430612522689 36056950937733322959392017)
            ·
              refine ⟨27042713203299992219544013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36056950937733322959392017 27042713203299992219544013)
              ·
                refine ⟨10141017451237497082329005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27042713203299992219544013 10141017451237497082329005)
                ·
                  refine ⟨3802881544214061405873377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10141017451237497082329005 3802881544214061405873377)
                  ·
                    refine ⟨2852161158160546054405033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3802881544214061405873377 2852161158160546054405033)
                    ·
                      refine ⟨2139120868620409540803775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852161158160546054405033 2139120868620409540803775)
                      ·
                        rfl

theorem cell23_4165923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_4165923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165923 prefixEnd_4165923 := by exact prefixLift 4165923
  have htrace : WordTrace (prefixWord ++ tailWord_4165923) baseStart_4165923 baseEnd_4165923 := by
    simpa [prefixWord, tailWord_4165923, baseEnd_4165923] using wordTrace_append hprefix tailTrace_4165923
  have hstable : (prefixWord ++ tailWord_4165923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165923).length < 2 ^ (prefixWord ++ tailWord_4165923).sum := by decide
  have hdescent : baseEnd_4165923 < baseStart_4165923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165940 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_4165940 : Nat := 118140960795 + 4165940 * 2 ^ 59
def prefixEnd_4165940 : Nat := 4983230072969 + 3 ^ 40 * 4165940 * 2
def baseEnd_4165940 : Nat := 2139129597791535974291197

theorem tailTrace_4165940 : CollatzResearch.WordTrace tailWord_4165940 prefixEnd_4165940 2139129597791535974291197 := by
  unfold tailWord_4165940
  simp only [CollatzResearch.WordTrace]
  refine ⟨75972157263759170376411637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101296209685012227168548849 75972157263759170376411637)
  ·
    refine ⟨7122389743477422222788591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75972157263759170376411637 7122389743477422222788591)
    ·
      refine ⟨10683584615216133334182887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122389743477422222788591 10683584615216133334182887)
      ·
        refine ⟨16025376922824200001274331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683584615216133334182887 16025376922824200001274331)
        ·
          refine ⟨24038065384236300001911497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16025376922824200001274331 24038065384236300001911497)
          ·
            refine ⟨18028549038177225001433623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24038065384236300001911497 18028549038177225001433623)
            ·
              refine ⟨27042823557265837502150435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18028549038177225001433623 27042823557265837502150435)
              ·
                refine ⟨40564235335898756253225653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27042823557265837502150435 40564235335898756253225653)
                ·
                  refine ⟨3802897062740508398739905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40564235335898756253225653 3802897062740508398739905)
                  ·
                    refine ⟨2852172797055381299054929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3802897062740508398739905 2852172797055381299054929)
                    ·
                      refine ⟨2139129597791535974291197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852172797055381299054929 2139129597791535974291197)
                      ·
                        rfl

theorem cell23_4165940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_4165940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165940 prefixEnd_4165940 := by exact prefixLift 4165940
  have htrace : WordTrace (prefixWord ++ tailWord_4165940) baseStart_4165940 baseEnd_4165940 := by
    simpa [prefixWord, tailWord_4165940, baseEnd_4165940] using wordTrace_append hprefix tailTrace_4165940
  have hstable : (prefixWord ++ tailWord_4165940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165940).length < 2 ^ (prefixWord ++ tailWord_4165940).sum := by decide
  have hdescent : baseEnd_4165940 < baseStart_4165940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4165946 : List Nat := [3, 1, 1, 1, 4, 3, 3, 7]
def baseStart_4165946 : Nat := 118140960795 + 4165946 * 2 ^ 59
def prefixEnd_4165946 : Nat := 4983230072969 + 3 ^ 40 * 4165946 * 2
def baseEnd_4165946 : Nat := 79227136247239368548747

theorem tailTrace_4165946 : CollatzResearch.WordTrace tailWord_4165946 prefixEnd_4165946 79227136247239368548747 := by
  unfold tailWord_4165946
  simp only [CollatzResearch.WordTrace]
  refine ⟨37986133341374150944385423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101296355576997735851694461 37986133341374150944385423)
  ·
    refine ⟨56979200012061226416578135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37986133341374150944385423 56979200012061226416578135)
    ·
      refine ⟨85468800018091839624867203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56979200012061226416578135 85468800018091839624867203)
      ·
        refine ⟨128203200027137759437300805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85468800018091839624867203 128203200027137759437300805)
        ·
          refine ⟨24038100005088329894493901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128203200027137759437300805 24038100005088329894493901)
          ·
            refine ⟨9014287501908123710435213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24038100005088329894493901 9014287501908123710435213)
            ·
              refine ⟨3380357813215546391413205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9014287501908123710435213 3380357813215546391413205)
              ·
                refine ⟨79227136247239368548747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3380357813215546391413205 79227136247239368548747)
                ·
                  rfl

theorem cell23_4165946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 7].length) (baseStart_4165946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4165946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4165946 prefixEnd_4165946 := by exact prefixLift 4165946
  have htrace : WordTrace (prefixWord ++ tailWord_4165946) baseStart_4165946 baseEnd_4165946 := by
    simpa [prefixWord, tailWord_4165946, baseEnd_4165946] using wordTrace_append hprefix tailTrace_4165946
  have hstable : (prefixWord ++ tailWord_4165946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4165946).length < 2 ^ (prefixWord ++ tailWord_4165946).sum := by decide
  have hdescent : baseEnd_4165946 < baseStart_4165946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4165946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166000 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 1, 3, 2]
def baseStart_4166000 : Nat := 118140960795 + 4166000 * 2 ^ 59
def prefixEnd_4166000 : Nat := 4983230072969 + 3 ^ 40 * 4166000 * 2
def baseEnd_4166000 : Nat := 2139160406630805739540921

theorem tailTrace_4166000 : CollatzResearch.WordTrace tailWord_4166000 prefixEnd_4166000 2139160406630805739540921 := by
  unfold tailWord_4166000
  simp only [CollatzResearch.WordTrace]
  refine ⟨75973251453650485500003727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101297668604867314000004969 75973251453650485500003727)
  ·
    refine ⟨113959877180475728250005591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75973251453650485500003727 113959877180475728250005591)
    ·
      refine ⟨170939815770713592375008387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113959877180475728250005591 170939815770713592375008387)
      ·
        refine ⟨256409723656070388562512581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170939815770713592375008387 256409723656070388562512581)
        ·
          refine ⟨48076823185513197855471109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256409723656070388562512581 48076823185513197855471109)
          ·
            refine ⟨9014404347283724597900833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48076823185513197855471109 9014404347283724597900833)
            ·
              refine ⟨6760803260462793448425625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9014404347283724597900833 6760803260462793448425625)
              ·
                refine ⟨5070602445347095086319219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6760803260462793448425625 5070602445347095086319219)
                ·
                  refine ⟨7605903668020642629478829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070602445347095086319219 7605903668020642629478829)
                  ·
                    refine ⟨2852213875507740986054561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7605903668020642629478829 2852213875507740986054561)
                    ·
                      refine ⟨2139160406630805739540921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852213875507740986054561 2139160406630805739540921)
                      ·
                        rfl

theorem cell23_4166000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 3, 2].length) (baseStart_4166000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166000 prefixEnd_4166000 := by exact prefixLift 4166000
  have htrace : WordTrace (prefixWord ++ tailWord_4166000) baseStart_4166000 baseEnd_4166000 := by
    simpa [prefixWord, tailWord_4166000, baseEnd_4166000] using wordTrace_append hprefix tailTrace_4166000
  have hstable : (prefixWord ++ tailWord_4166000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166000).length < 2 ^ (prefixWord ++ tailWord_4166000).sum := by decide
  have hdescent : baseEnd_4166000 < baseStart_4166000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166113 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 3, 4]
def baseStart_4166113 : Nat := 118140960795 + 4166113 * 2 ^ 59
def prefixEnd_4166113 : Nat := 4983230072969 + 3 ^ 40 * 4166113 * 2
def baseEnd_4166113 : Nat := 713072809981587932475967

theorem tailTrace_4166113 : CollatzResearch.WordTrace tailWord_4166113 prefixEnd_4166113 713072809981587932475967 := by
  unfold tailWord_4166113
  simp only [CollatzResearch.WordTrace]
  refine ⟨151950624355891591298870993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101300416237261060865913995 151950624355891591298870993)
  ·
    refine ⟨113962968266918693474153245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151950624355891591298870993 113962968266918693474153245)
    ·
      refine ⟨42736113100094510052807467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113962968266918693474153245 42736113100094510052807467)
      ·
        refine ⟨64104169650141765079211201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42736113100094510052807467 64104169650141765079211201)
        ·
          refine ⟨48078127237606323809408401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64104169650141765079211201 48078127237606323809408401)
          ·
            refine ⟨36058595428204742857056301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48078127237606323809408401 36058595428204742857056301)
            ·
              refine ⟨13521973285576778571396113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36058595428204742857056301 13521973285576778571396113)
              ·
                refine ⟨10141479964182583928547085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13521973285576778571396113 10141479964182583928547085)
                ·
                  refine ⟨3803054986568468973205157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10141479964182583928547085 3803054986568468973205157)
                  ·
                    refine ⟨713072809981587932475967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803054986568468973205157 713072809981587932475967)
                    ·
                      rfl

theorem cell23_4166113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_4166113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166113 prefixEnd_4166113 := by exact prefixLift 4166113
  have htrace : WordTrace (prefixWord ++ tailWord_4166113) baseStart_4166113 baseEnd_4166113 := by
    simpa [prefixWord, tailWord_4166113, baseEnd_4166113] using wordTrace_append hprefix tailTrace_4166113
  have hstable : (prefixWord ++ tailWord_4166113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166113).length < 2 ^ (prefixWord ++ tailWord_4166113).sum := by decide
  have hdescent : baseEnd_4166113 < baseStart_4166113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166117 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_4166117 : Nat := 118140960795 + 4166117 * 2 ^ 59
def prefixEnd_4166117 : Nat := 4983230072969 + 3 ^ 40 * 4166117 * 2
def baseEnd_4166117 : Nat := 713073494622460593925961

theorem tailTrace_4166117 : CollatzResearch.WordTrace tailWord_4166117 prefixEnd_4166117 713073494622460593925961 := by
  unfold tailWord_4166117
  simp only [CollatzResearch.WordTrace]
  refine ⟨151950770247877099982016605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101300513498584733321344403 151950770247877099982016605)
  ·
    refine ⟨56981538842953912493256227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151950770247877099982016605 56981538842953912493256227)
    ·
      refine ⟨85472308264430868739884341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56981538842953912493256227 85472308264430868739884341)
      ·
        refine ⟨8013028899790393944364157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85472308264430868739884341 8013028899790393944364157)
        ·
          refine ⟨3004885837421397729136559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8013028899790393944364157 3004885837421397729136559)
          ·
            refine ⟨4507328756132096593704839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004885837421397729136559 4507328756132096593704839)
            ·
              refine ⟨6760993134198144890557259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507328756132096593704839 6760993134198144890557259)
              ·
                refine ⟨10141489701297217335835889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760993134198144890557259 10141489701297217335835889)
                ·
                  refine ⟨7606117275972913001876917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10141489701297217335835889 7606117275972913001876917)
                  ·
                    refine ⟨713073494622460593925961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7606117275972913001876917 713073494622460593925961)
                    ·
                      rfl

theorem cell23_4166117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_4166117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166117 prefixEnd_4166117 := by exact prefixLift 4166117
  have htrace : WordTrace (prefixWord ++ tailWord_4166117) baseStart_4166117 baseEnd_4166117 := by
    simpa [prefixWord, tailWord_4166117, baseEnd_4166117] using wordTrace_append hprefix tailTrace_4166117
  have hstable : (prefixWord ++ tailWord_4166117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166117).length < 2 ^ (prefixWord ++ tailWord_4166117).sum := by decide
  have hdescent : baseEnd_4166117 < baseStart_4166117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166120 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_4166120 : Nat := 118140960795 + 4166120 * 2 ^ 59
def prefixEnd_4166120 : Nat := 4983230072969 + 3 ^ 40 * 4166120 * 2
def baseEnd_4166120 : Nat := 2139222024309345270040369

theorem tailTrace_4166120 : CollatzResearch.WordTrace tailWord_4166120 prefixEnd_4166120 2139222024309345270040369 := by
  unfold tailWord_4166120
  simp only [CollatzResearch.WordTrace]
  refine ⟨75975439833433115747187907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101300586444577487662917209 75975439833433115747187907)
  ·
    refine ⟨113963159750149673620781861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75975439833433115747187907 113963159750149673620781861)
    ·
      refine ⟨21368092453153063803896599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113963159750149673620781861 21368092453153063803896599)
      ·
        refine ⟨32052138679729595705844899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21368092453153063803896599 32052138679729595705844899)
        ·
          refine ⟨48078208019594393558767349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32052138679729595705844899 48078208019594393558767349)
          ·
            refine ⟨4507332001836974396134439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48078208019594393558767349 4507332001836974396134439)
            ·
              refine ⟨6760998002755461594201659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507332001836974396134439 6760998002755461594201659)
              ·
                refine ⟨10141497004133192391302489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760998002755461594201659 10141497004133192391302489)
                ·
                  refine ⟨7606122753099894293476867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10141497004133192391302489 7606122753099894293476867)
                  ·
                    refine ⟨11409184129649841440215301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7606122753099894293476867 11409184129649841440215301)
                    ·
                      refine ⟨2139222024309345270040369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11409184129649841440215301 2139222024309345270040369)
                      ·
                        rfl

theorem cell23_4166120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_4166120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166120 prefixEnd_4166120 := by exact prefixLift 4166120
  have htrace : WordTrace (prefixWord ++ tailWord_4166120) baseStart_4166120 baseEnd_4166120 := by
    simpa [prefixWord, tailWord_4166120, baseEnd_4166120] using wordTrace_append hprefix tailTrace_4166120
  have hstable : (prefixWord ++ tailWord_4166120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166120).length < 2 ^ (prefixWord ++ tailWord_4166120).sum := by decide
  have hdescent : baseEnd_4166120 < baseStart_4166120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166157 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_4166157 : Nat := 118140960795 + 4166157 * 2 ^ 59
def prefixEnd_4166157 : Nat := 4983230072969 + 3 ^ 40 * 4166157 * 2
def baseEnd_4166157 : Nat := 2139241023093561625277699

theorem tailTrace_4166157 : CollatzResearch.WordTrace tailWord_4166157 prefixEnd_4166157 2139241023093561625277699 := by
  unfold tailWord_4166157
  simp only [CollatzResearch.WordTrace]
  refine ⟨151952229167732186813472725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101301486111821457875648483 151952229167732186813472725)
  ·
    refine ⟨3561380371118723128440767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 151952229167732186813472725 3561380371118723128440767)
    ·
      refine ⟨5342070556678084692661151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3561380371118723128440767 5342070556678084692661151)
      ·
        refine ⟨8013105835017127038991727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5342070556678084692661151 8013105835017127038991727)
        ·
          refine ⟨12019658752525690558487591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8013105835017127038991727 12019658752525690558487591)
          ·
            refine ⟨18029488128788535837731387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12019658752525690558487591 18029488128788535837731387)
            ·
              refine ⟨27044232193182803756597081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18029488128788535837731387 27044232193182803756597081)
              ·
                refine ⟨20283174144887102817447811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27044232193182803756597081 20283174144887102817447811)
                ·
                  refine ⟨30424761217330654226171717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20283174144887102817447811 30424761217330654226171717)
                  ·
                    refine ⟨5704642728249497667407197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30424761217330654226171717 5704642728249497667407197)
                    ·
                      refine ⟨2139241023093561625277699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5704642728249497667407197 2139241023093561625277699)
                      ·
                        rfl

theorem cell23_4166157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_4166157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166157 prefixEnd_4166157 := by exact prefixLift 4166157
  have htrace : WordTrace (prefixWord ++ tailWord_4166157) baseStart_4166157 baseEnd_4166157 := by
    simpa [prefixWord, tailWord_4166157, baseEnd_4166157] using wordTrace_append hprefix tailTrace_4166157
  have hstable : (prefixWord ++ tailWord_4166157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166157).length < 2 ^ (prefixWord ++ tailWord_4166157).sum := by decide
  have hdescent : baseEnd_4166157 < baseStart_4166157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166163 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 3, 5, 2]
def baseStart_4166163 : Nat := 118140960795 + 4166163 * 2 ^ 59
def prefixEnd_4166163 : Nat := 4983230072969 + 3 ^ 40 * 4166163 * 2
def baseEnd_4166163 : Nat := 2139244103977488601802671

theorem tailTrace_4166163 : CollatzResearch.WordTrace tailWord_4166163 prefixEnd_4166163 2139244103977488601802671 := by
  unfold tailWord_4166163
  simp only [CollatzResearch.WordTrace]
  refine ⟨151952448005710449838191143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101301632003806966558794095 151952448005710449838191143)
  ·
    refine ⟨227928672008565674757286715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151952448005710449838191143 227928672008565674757286715)
    ·
      refine ⟨341893008012848512135930073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227928672008565674757286715 341893008012848512135930073)
      ·
        refine ⟨256419756009636384101947555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341893008012848512135930073 256419756009636384101947555)
        ·
          refine ⟨384629634014454576152921333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256419756009636384101947555 384629634014454576152921333)
          ·
            refine ⟨36059028188855116514336375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384629634014454576152921333 36059028188855116514336375)
            ·
              refine ⟨54088542283282674771504563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36059028188855116514336375 54088542283282674771504563)
              ·
                refine ⟨81132813424924012157256845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54088542283282674771504563 81132813424924012157256845)
                ·
                  refine ⟨30424805034346504558971317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81132813424924012157256845 30424805034346504558971317)
                  ·
                    refine ⟨2852325471969984802403561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30424805034346504558971317 2852325471969984802403561)
                    ·
                      refine ⟨2139244103977488601802671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852325471969984802403561 2139244103977488601802671)
                      ·
                        rfl

theorem cell23_4166163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 5, 2].length) (baseStart_4166163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166163 prefixEnd_4166163 := by exact prefixLift 4166163
  have htrace : WordTrace (prefixWord ++ tailWord_4166163) baseStart_4166163 baseEnd_4166163 := by
    simpa [prefixWord, tailWord_4166163, baseEnd_4166163] using wordTrace_append hprefix tailTrace_4166163
  have hstable : (prefixWord ++ tailWord_4166163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166163).length < 2 ^ (prefixWord ++ tailWord_4166163).sum := by decide
  have hdescent : baseEnd_4166163 < baseStart_4166163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166170 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3]
def baseStart_4166170 : Nat := 118140960795 + 4166170 * 2 ^ 59
def prefixEnd_4166170 : Nat := 4983230072969 + 3 ^ 40 * 4166170 * 2
def baseEnd_4166170 : Nat := 2139247698342070074415139

theorem tailTrace_4166170 : CollatzResearch.WordTrace tailWord_4166170 prefixEnd_4166170 2139247698342070074415139 := by
  unfold tailWord_4166170
  simp only [CollatzResearch.WordTrace]
  refine ⟨37988175829171272508423991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101301802211123393355797309 37988175829171272508423991)
  ·
    refine ⟨56982263743756908762635987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37988175829171272508423991 56982263743756908762635987)
    ·
      refine ⟨85473395615635363143953981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56982263743756908762635987 85473395615635363143953981)
      ·
        refine ⟨32052523355863261178982743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85473395615635363143953981 32052523355863261178982743)
        ·
          refine ⟨48078785033794891768474115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32052523355863261178982743 48078785033794891768474115)
          ·
            refine ⟨72118177550692337652711173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48078785033794891768474115 72118177550692337652711173)
            ·
              refine ⟨13522158290754813309883345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72118177550692337652711173 13522158290754813309883345)
              ·
                refine ⟨10141618718066109982412509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13522158290754813309883345 10141618718066109982412509)
                ·
                  refine ⟨3803107019274791243404691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10141618718066109982412509 3803107019274791243404691)
                  ·
                    refine ⟨5704660528912186865107037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3803107019274791243404691 5704660528912186865107037)
                    ·
                      refine ⟨2139247698342070074415139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5704660528912186865107037 2139247698342070074415139)
                      ·
                        rfl

theorem cell23_4166170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_4166170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166170 prefixEnd_4166170 := by exact prefixLift 4166170
  have htrace : WordTrace (prefixWord ++ tailWord_4166170) baseStart_4166170 baseEnd_4166170 := by
    simpa [prefixWord, tailWord_4166170, baseEnd_4166170] using wordTrace_append hprefix tailTrace_4166170
  have hstable : (prefixWord ++ tailWord_4166170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166170).length < 2 ^ (prefixWord ++ tailWord_4166170).sum := by decide
  have hdescent : baseEnd_4166170 < baseStart_4166170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166213 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_4166213 : Nat := 118140960795 + 4166213 * 2 ^ 59
def prefixEnd_4166213 : Nat := 4983230072969 + 3 ^ 40 * 4166213 * 2
def baseEnd_4166213 : Nat := 2139269778010213406177441

theorem tailTrace_4166213 : CollatzResearch.WordTrace tailWord_4166213 prefixEnd_4166213 2139269778010213406177441 := by
  unfold tailWord_4166213
  simp only [CollatzResearch.WordTrace]
  refine ⟨151954271655529308377511293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101302847770352872251674195 151954271655529308377511293)
  ·
    refine ⟨56982851870823490641566735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151954271655529308377511293 56982851870823490641566735)
    ·
      refine ⟨85474277806235235962350103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56982851870823490641566735 85474277806235235962350103)
      ·
        refine ⟨128211416709352853943525155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85474277806235235962350103 128211416709352853943525155)
        ·
          refine ⟨192317125064029280915287733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128211416709352853943525155 192317125064029280915287733)
          ·
            refine ⟨18029730474752745085808225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192317125064029280915287733 18029730474752745085808225)
            ·
              refine ⟨13522297856064558814356169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18029730474752745085808225 13522297856064558814356169)
              ·
                refine ⟨10141723392048419110767127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13522297856064558814356169 10141723392048419110767127)
                ·
                  refine ⟨15212585088072628666150691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10141723392048419110767127 15212585088072628666150691)
                  ·
                    refine ⟨22818877632108942999226037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15212585088072628666150691 22818877632108942999226037)
                    ·
                      refine ⟨2139269778010213406177441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22818877632108942999226037 2139269778010213406177441)
                      ·
                        rfl

theorem cell23_4166213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_4166213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166213 prefixEnd_4166213 := by exact prefixLift 4166213
  have htrace : WordTrace (prefixWord ++ tailWord_4166213) baseStart_4166213 baseEnd_4166213 := by
    simpa [prefixWord, tailWord_4166213, baseEnd_4166213] using wordTrace_append hprefix tailTrace_4166213
  have hstable : (prefixWord ++ tailWord_4166213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166213).length < 2 ^ (prefixWord ++ tailWord_4166213).sum := by decide
  have hdescent : baseEnd_4166213 < baseStart_4166213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166220 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_4166220 : Nat := 118140960795 + 4166220 * 2 ^ 59
def prefixEnd_4166220 : Nat := 4983230072969 + 3 ^ 40 * 4166220 * 2
def baseEnd_4166220 : Nat := 713091124124931626263303

theorem tailTrace_4166220 : CollatzResearch.WordTrace tailWord_4166220 prefixEnd_4166220 713091124124931626263303 := by
  unfold tailWord_4166220
  simp only [CollatzResearch.WordTrace]
  refine ⟨75977263483251974286508057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101303017977669299048677409 75977263483251974286508057)
  ·
    refine ⟨56982947612438980714881043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75977263483251974286508057 56982947612438980714881043)
    ·
      refine ⟨85474421418658471072321565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56982947612438980714881043 85474421418658471072321565)
      ·
        refine ⟨32052908031996926652120587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85474421418658471072321565 32052908031996926652120587)
        ·
          refine ⟨48079362047995389978180881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32052908031996926652120587 48079362047995389978180881)
          ·
            refine ⟨36059521535996542483635661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48079362047995389978180881 36059521535996542483635661)
            ·
              refine ⟨13522320575998703431363373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36059521535996542483635661 13522320575998703431363373)
              ·
                refine ⟨5070870215999513786761265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13522320575998703431363373 5070870215999513786761265)
                ·
                  refine ⟨3803152661999635340070949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5070870215999513786761265 3803152661999635340070949)
                  ·
                    refine ⟨713091124124931626263303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803152661999635340070949 713091124124931626263303)
                    ·
                      rfl

theorem cell23_4166220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_4166220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166220 prefixEnd_4166220 := by exact prefixLift 4166220
  have htrace : WordTrace (prefixWord ++ tailWord_4166220) baseStart_4166220 baseEnd_4166220 := by
    simpa [prefixWord, tailWord_4166220, baseEnd_4166220] using wordTrace_append hprefix tailTrace_4166220
  have hstable : (prefixWord ++ tailWord_4166220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166220).length < 2 ^ (prefixWord ++ tailWord_4166220).sum := by decide
  have hdescent : baseEnd_4166220 < baseStart_4166220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166244 : List Nat := [2, 3, 1, 1, 2, 2, 2, 5, 1, 2, 2]
def baseStart_4166244 : Nat := 118140960795 + 4166244 * 2 ^ 59
def prefixEnd_4166244 : Nat := 4983230072969 + 3 ^ 40 * 4166244 * 2
def baseEnd_4166244 : Nat := 2139285695910502784889799

theorem tailTrace_4166244 : CollatzResearch.WordTrace tailWord_4166244 prefixEnd_4166244 2139285695910502784889799 := by
  unfold tailWord_4166244
  simp only [CollatzResearch.WordTrace]
  refine ⟨75977701159208500335944893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101303601545611333781259857 75977701159208500335944893)
  ·
    refine ⟨28491637934703187625979335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75977701159208500335944893 28491637934703187625979335)
    ·
      refine ⟨42737456902054781438969003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28491637934703187625979335 42737456902054781438969003)
      ·
        refine ⟨64106185353082172158453505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42737456902054781438969003 64106185353082172158453505)
        ·
          refine ⟨48079639014811629118840129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64106185353082172158453505 48079639014811629118840129)
          ·
            refine ⟨36059729261108721839130097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48079639014811629118840129 36059729261108721839130097)
            ·
              refine ⟨27044796945831541379347573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36059729261108721839130097 27044796945831541379347573)
              ·
                refine ⟨2535449713671707004313835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27044796945831541379347573 2535449713671707004313835)
                ·
                  refine ⟨3803174570507560506470753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535449713671707004313835 3803174570507560506470753)
                  ·
                    refine ⟨2852380927880670379853065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3803174570507560506470753 2852380927880670379853065)
                    ·
                      refine ⟨2139285695910502784889799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852380927880670379853065 2139285695910502784889799)
                      ·
                        rfl

theorem cell23_4166244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_4166244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166244 prefixEnd_4166244 := by exact prefixLift 4166244
  have htrace : WordTrace (prefixWord ++ tailWord_4166244) baseStart_4166244 baseEnd_4166244 := by
    simpa [prefixWord, tailWord_4166244, baseEnd_4166244] using wordTrace_append hprefix tailTrace_4166244
  have hstable : (prefixWord ++ tailWord_4166244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166244).length < 2 ^ (prefixWord ++ tailWord_4166244).sum := by decide
  have hdescent : baseEnd_4166244 < baseStart_4166244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166277 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 3]
def baseStart_4166277 : Nat := 118140960795 + 4166277 * 2 ^ 59
def prefixEnd_4166277 : Nat := 4983230072969 + 3 ^ 40 * 4166277 * 2
def baseEnd_4166277 : Nat := 2139302640772101155777147

theorem tailTrace_4166277 : CollatzResearch.WordTrace tailWord_4166277 prefixEnd_4166277 2139302640772101155777147 := by
  unfold tailWord_4166277
  simp only [CollatzResearch.WordTrace]
  refine ⟨151956605927297447307841085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101304403951531631538560723 151956605927297447307841085)
  ·
    refine ⟨56983727222736542740440407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151956605927297447307841085 56983727222736542740440407)
    ·
      refine ⟨85475590834104814110660611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56983727222736542740440407 85475590834104814110660611)
      ·
        refine ⟨128213386251157221165990917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85475590834104814110660611 128213386251157221165990917)
        ·
          refine ⟨24040009922091978968623297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128213386251157221165990917 24040009922091978968623297)
          ·
            refine ⟨18030007441568984226467473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24040009922091978968623297 18030007441568984226467473)
            ·
              refine ⟨13522505581176738169850605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18030007441568984226467473 13522505581176738169850605)
              ·
                refine ⟨5070939592941276813693977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13522505581176738169850605 5070939592941276813693977)
                ·
                  refine ⟨3803204694705957610270483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5070939592941276813693977 3803204694705957610270483)
                  ·
                    refine ⟨5704807042058936415405725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3803204694705957610270483 5704807042058936415405725)
                    ·
                      refine ⟨2139302640772101155777147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5704807042058936415405725 2139302640772101155777147)
                      ·
                        rfl

theorem cell23_4166277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_4166277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166277 prefixEnd_4166277 := by exact prefixLift 4166277
  have htrace : WordTrace (prefixWord ++ tailWord_4166277) baseStart_4166277 baseEnd_4166277 := by
    simpa [prefixWord, tailWord_4166277, baseEnd_4166277] using wordTrace_append hprefix tailTrace_4166277
  have hstable : (prefixWord ++ tailWord_4166277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166277).length < 2 ^ (prefixWord ++ tailWord_4166277).sum := by decide
  have hdescent : baseEnd_4166277 < baseStart_4166277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166298 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4166298 : Nat := 118140960795 + 4166298 * 2 ^ 59
def prefixEnd_4166298 : Nat := 4983230072969 + 3 ^ 40 * 4166298 * 2
def baseEnd_4166298 : Nat := 2139313423865845573614551

theorem tailTrace_4166298 : CollatzResearch.WordTrace tailWord_4166298 prefixEnd_4166298 2139313423865845573614551 := by
  unfold tailWord_4166298
  simp only [CollatzResearch.WordTrace]
  refine ⟨37989342965055341973588887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101304914573480911929570365 37989342965055341973588887)
  ·
    refine ⟨56984014447583012960383331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37989342965055341973588887 56984014447583012960383331)
    ·
      refine ⟨85476021671374519440574997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56984014447583012960383331 85476021671374519440574997)
      ·
        refine ⟨4006688515845680598776953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85476021671374519440574997 4006688515845680598776953)
        ·
          refine ⟨3005016386884260449082715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4006688515845680598776953 3005016386884260449082715)
          ·
            refine ⟨4507524580326390673624073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005016386884260449082715 4507524580326390673624073)
            ·
              refine ⟨3380643435244793005218055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4507524580326390673624073 3380643435244793005218055)
              ·
                refine ⟨5070965152867189507827083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380643435244793005218055 5070965152867189507827083)
                ·
                  refine ⟨7606447729300784261740625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070965152867189507827083 7606447729300784261740625)
                  ·
                    refine ⟨5704835796975588196305469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606447729300784261740625 5704835796975588196305469)
                    ·
                      refine ⟨2139313423865845573614551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5704835796975588196305469 2139313423865845573614551)
                      ·
                        rfl

theorem cell23_4166298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4166298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166298 prefixEnd_4166298 := by exact prefixLift 4166298
  have htrace : WordTrace (prefixWord ++ tailWord_4166298) baseStart_4166298 baseEnd_4166298 := by
    simpa [prefixWord, tailWord_4166298, baseEnd_4166298] using wordTrace_append hprefix tailTrace_4166298
  have hstable : (prefixWord ++ tailWord_4166298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166298).length < 2 ^ (prefixWord ++ tailWord_4166298).sum := by decide
  have hdescent : baseEnd_4166298 < baseStart_4166298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166304 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 1, 3, 2]
def baseStart_4166304 : Nat := 118140960795 + 4166304 * 2 ^ 59
def prefixEnd_4166304 : Nat := 4983230072969 + 3 ^ 40 * 4166304 * 2
def baseEnd_4166304 : Nat := 2139316504749772550139523

theorem tailTrace_4166304 : CollatzResearch.WordTrace tailWord_4166304 prefixEnd_4166304 2139316504749772550139523 := by
  unfold tailWord_4166304
  simp only [CollatzResearch.WordTrace]
  refine ⟨75978795349099815459536983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101305060465466420612715977 75978795349099815459536983)
  ·
    refine ⟨113968193023649723189305475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75978795349099815459536983 113968193023649723189305475)
    ·
      refine ⟨170952289535474584783958213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113968193023649723189305475 170952289535474584783958213)
      ·
        refine ⟨32053554287901484646992165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170952289535474584783958213 32053554287901484646992165)
        ·
          refine ⟨6010041428981528371311031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32053554287901484646992165 6010041428981528371311031)
          ·
            refine ⟨9015062143472292556966547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6010041428981528371311031 9015062143472292556966547)
            ·
              refine ⟨13522593215208438835449821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9015062143472292556966547 13522593215208438835449821)
              ·
                refine ⟨5070972455703164563293683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13522593215208438835449821 5070972455703164563293683)
                ·
                  refine ⟨7606458683554746844940525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070972455703164563293683 7606458683554746844940525)
                  ·
                    refine ⟨2852422006333030066852697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7606458683554746844940525 2852422006333030066852697)
                    ·
                      refine ⟨2139316504749772550139523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852422006333030066852697 2139316504749772550139523)
                      ·
                        rfl

theorem cell23_4166304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_4166304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166304 prefixEnd_4166304 := by exact prefixLift 4166304
  have htrace : WordTrace (prefixWord ++ tailWord_4166304) baseStart_4166304 baseEnd_4166304 := by
    simpa [prefixWord, tailWord_4166304, baseEnd_4166304] using wordTrace_append hprefix tailTrace_4166304
  have hstable : (prefixWord ++ tailWord_4166304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166304).length < 2 ^ (prefixWord ++ tailWord_4166304).sum := by decide
  have hdescent : baseEnd_4166304 < baseStart_4166304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166313 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_4166313 : Nat := 118140960795 + 4166313 * 2 ^ 59
def prefixEnd_4166313 : Nat := 4983230072969 + 3 ^ 40 * 4166313 * 2
def baseEnd_4166313 : Nat := 2139321126075663014926981

theorem tailTrace_4166313 : CollatzResearch.WordTrace tailWord_4166313 prefixEnd_4166313 2139321126075663014926981 := by
  unfold tailWord_4166313
  simp only [CollatzResearch.WordTrace]
  refine ⟨151957918955167025456151593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101305279303444683637434395 151957918955167025456151593)
  ·
    refine ⟨113968439216375269092113695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151957918955167025456151593 113968439216375269092113695)
    ·
      refine ⟨170952658824562903638170543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113968439216375269092113695 170952658824562903638170543)
      ·
        refine ⟨256428988236844355457255815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170952658824562903638170543 256428988236844355457255815)
        ·
          refine ⟨384643482355266533185883723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256428988236844355457255815 384643482355266533185883723)
          ·
            refine ⟨576965223532899799778825585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384643482355266533185883723 576965223532899799778825585)
            ·
              refine ⟨432723917649674849834119189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576965223532899799778825585 432723917649674849834119189)
              ·
                refine ⟨20283933639828508585974337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 432723917649674849834119189 20283933639828508585974337)
                ·
                  refine ⟨15212950229871381439480753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20283933639828508585974337 15212950229871381439480753)
                  ·
                    refine ⟨11409712672403536079610565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15212950229871381439480753 11409712672403536079610565)
                    ·
                      refine ⟨2139321126075663014926981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11409712672403536079610565 2139321126075663014926981)
                      ·
                        rfl

theorem cell23_4166313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_4166313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166313 prefixEnd_4166313 := by exact prefixLift 4166313
  have htrace : WordTrace (prefixWord ++ tailWord_4166313) baseStart_4166313 baseEnd_4166313 := by
    simpa [prefixWord, tailWord_4166313, baseEnd_4166313] using wordTrace_append hprefix tailTrace_4166313
  have hstable : (prefixWord ++ tailWord_4166313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166313).length < 2 ^ (prefixWord ++ tailWord_4166313).sum := by decide
  have hdescent : baseEnd_4166313 < baseStart_4166313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166323 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 7]
def baseStart_4166323 : Nat := 118140960795 + 4166323 * 2 ^ 59
def prefixEnd_4166323 : Nat := 4983230072969 + 3 ^ 40 * 4166323 * 2
def baseEnd_4166323 : Nat := 237702917875800886200215

theorem tailTrace_4166323 : CollatzResearch.WordTrace tailWord_4166323 prefixEnd_4166323 237702917875800886200215 := by
  unfold tailWord_4166323
  simp only [CollatzResearch.WordTrace]
  refine ⟨151958283685130797164015623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101305522456753864776010415 151958283685130797164015623)
  ·
    refine ⟨227937425527696195746023435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151958283685130797164015623 227937425527696195746023435)
    ·
      refine ⟨341906138291544293619035153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227937425527696195746023435 341906138291544293619035153)
      ·
        refine ⟨256429603718658220214276365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341906138291544293619035153 256429603718658220214276365)
        ·
          refine ⟨96161101394496832580353637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256429603718658220214276365 96161101394496832580353637)
          ·
            refine ⟨18030206511468156108816307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96161101394496832580353637 18030206511468156108816307)
            ·
              refine ⟨27045309767202234163224461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18030206511468156108816307 27045309767202234163224461)
              ·
                refine ⟨10141991162700837811209173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27045309767202234163224461 10141991162700837811209173)
                ·
                  refine ⟨237702917875800886200215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10141991162700837811209173 237702917875800886200215)
                  ·
                    rfl

theorem cell23_4166323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 7].length) (baseStart_4166323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166323 prefixEnd_4166323 := by exact prefixLift 4166323
  have htrace : WordTrace (prefixWord ++ tailWord_4166323) baseStart_4166323 baseEnd_4166323 := by
    simpa [prefixWord, tailWord_4166323, baseEnd_4166323] using wordTrace_append hprefix tailTrace_4166323
  have hstable : (prefixWord ++ tailWord_4166323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166323).length < 2 ^ (prefixWord ++ tailWord_4166323).sum := by decide
  have hdescent : baseEnd_4166323 < baseStart_4166323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166340 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 7]
def baseStart_4166340 : Nat := 118140960795 + 4166340 * 2 ^ 59
def prefixEnd_4166340 : Nat := 4983230072969 + 3 ^ 40 * 4166340 * 2
def baseEnd_4166340 : Nat := 237703887783703823254373

theorem tailTrace_4166340 : CollatzResearch.WordTrace tailWord_4166340 prefixEnd_4166340 237703887783703823254373 := by
  unfold tailWord_4166340
  simp only [CollatzResearch.WordTrace]
  refine ⟨75979451863034604533692237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101305935817379472711589649 75979451863034604533692237)
  ·
    refine ⟨28492294448637976700134589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75979451863034604533692237 28492294448637976700134589)
    ·
      refine ⟨10684610418239241262550471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28492294448637976700134589 10684610418239241262550471)
      ·
        refine ⟨16026915627358861893825707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10684610418239241262550471 16026915627358861893825707)
        ·
          refine ⟨24040373441038292840738561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16026915627358861893825707 24040373441038292840738561)
          ·
            refine ⟨18030280080778719630553921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24040373441038292840738561 18030280080778719630553921)
            ·
              refine ⟨13522710060584039722915441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18030280080778719630553921 13522710060584039722915441)
              ·
                refine ⟨10142032545438029792186581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13522710060584039722915441 10142032545438029792186581)
                ·
                  refine ⟨237703887783703823254373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10142032545438029792186581 237703887783703823254373)
                  ·
                    rfl

theorem cell23_4166340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_4166340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166340 prefixEnd_4166340 := by exact prefixLift 4166340
  have htrace : WordTrace (prefixWord ++ tailWord_4166340) baseStart_4166340 baseEnd_4166340 := by
    simpa [prefixWord, tailWord_4166340, baseEnd_4166340] using wordTrace_append hprefix tailTrace_4166340
  have hstable : (prefixWord ++ tailWord_4166340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166340).length < 2 ^ (prefixWord ++ tailWord_4166340).sum := by decide
  have hdescent : baseEnd_4166340 < baseStart_4166340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166353 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 1, 7]
def baseStart_4166353 : Nat := 118140960795 + 4166353 * 2 ^ 59
def prefixEnd_4166353 : Nat := 4983230072969 + 3 ^ 40 * 4166353 * 2
def baseEnd_4166353 : Nat := 713113888433947619475599

theorem tailTrace_4166353 : CollatzResearch.WordTrace tailWord_4166353 prefixEnd_4166353 713113888433947619475599 := by
  unfold tailWord_4166353
  simp only [CollatzResearch.WordTrace]
  refine ⟨151959377875022112287607713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101306251916681408191738475 151959377875022112287607713)
  ·
    refine ⟨113969533406266584215705785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151959377875022112287607713 113969533406266584215705785)
    ·
      refine ⟨85477150054699938161779339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113969533406266584215705785 85477150054699938161779339)
      ·
        refine ⟨128215725082049907242669009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85477150054699938161779339 128215725082049907242669009)
        ·
          refine ⟨96161793811537430432001757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128215725082049907242669009 96161793811537430432001757)
          ·
            refine ⟨36060672679326536412000659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96161793811537430432001757 36060672679326536412000659)
            ·
              refine ⟨54091009018989804618000989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36060672679326536412000659 54091009018989804618000989)
              ·
                refine ⟨20284128382121176731750371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54091009018989804618000989 20284128382121176731750371)
                ·
                  refine ⟨30426192573181765097625557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20284128382121176731750371 30426192573181765097625557)
                  ·
                    refine ⟨713113888433947619475599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30426192573181765097625557 713113888433947619475599)
                    ·
                      rfl

theorem cell23_4166353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_4166353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166353 prefixEnd_4166353 := by exact prefixLift 4166353
  have htrace : WordTrace (prefixWord ++ tailWord_4166353) baseStart_4166353 baseEnd_4166353 := by
    simpa [prefixWord, tailWord_4166353, baseEnd_4166353] using wordTrace_append hprefix tailTrace_4166353
  have hstable : (prefixWord ++ tailWord_4166353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166353).length < 2 ^ (prefixWord ++ tailWord_4166353).sum := by decide
  have hdescent : baseEnd_4166353 < baseStart_4166353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166393 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_4166393 : Nat := 118140960795 + 4166393 * 2 ^ 59
def prefixEnd_4166393 : Nat := 4983230072969 + 3 ^ 40 * 4166393 * 2
def baseEnd_4166393 : Nat := 2139362204528022701926613

theorem tailTrace_4166393 : CollatzResearch.WordTrace tailWord_4166393 prefixEnd_4166393 2139362204528022701926613 := by
  unfold tailWord_4166393
  simp only [CollatzResearch.WordTrace]
  refine ⟨151960836794877199119063833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101307224529918132746042555 151960836794877199119063833)
  ·
    refine ⟨113970627596157899339297875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151960836794877199119063833 113970627596157899339297875)
    ·
      refine ⟨170955941394236849008946813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113970627596157899339297875 170955941394236849008946813)
      ·
        refine ⟨64108478022838818378355055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170955941394236849008946813 64108478022838818378355055)
        ·
          refine ⟨96162717034258227567532583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64108478022838818378355055 96162717034258227567532583)
          ·
            refine ⟨144244075551387341351298875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96162717034258227567532583 144244075551387341351298875)
            ·
              refine ⟨216366113327081012026948313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144244075551387341351298875 216366113327081012026948313)
              ·
                refine ⟨162274584995310759020211235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216366113327081012026948313 162274584995310759020211235)
                ·
                  refine ⟨243411877492966138530316853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162274584995310759020211235 243411877492966138530316853)
                  ·
                    refine ⟨22819863514965575487217205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 243411877492966138530316853 22819863514965575487217205)
                    ·
                      refine ⟨2139362204528022701926613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22819863514965575487217205 2139362204528022701926613)
                      ·
                        rfl

theorem cell23_4166393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_4166393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166393 prefixEnd_4166393 := by exact prefixLift 4166393
  have htrace : WordTrace (prefixWord ++ tailWord_4166393) baseStart_4166393 baseEnd_4166393 := by
    simpa [prefixWord, tailWord_4166393, baseEnd_4166393] using wordTrace_append hprefix tailTrace_4166393
  have hstable : (prefixWord ++ tailWord_4166393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166393).length < 2 ^ (prefixWord ++ tailWord_4166393).sum := by decide
  have hdescent : baseEnd_4166393 < baseStart_4166393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166403 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 6]
def baseStart_4166403 : Nat := 118140960795 + 4166403 * 2 ^ 59
def prefixEnd_4166403 : Nat := 4983230072969 + 3 ^ 40 * 4166403 * 2
def baseEnd_4166403 : Nat := 2139367339334567662801567

theorem tailTrace_4166403 : CollatzResearch.WordTrace tailWord_4166403 prefixEnd_4166403 2139367339334567662801567 := by
  unfold tailWord_4166403
  simp only [CollatzResearch.WordTrace]
  refine ⟨151961201524840970826927863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101307467683227313884618575 151961201524840970826927863)
  ·
    refine ⟨227941802287261456240391795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151961201524840970826927863 227941802287261456240391795)
    ·
      refine ⟨341912703430892184360587693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227941802287261456240391795 341912703430892184360587693)
      ·
        refine ⟨128217263786584569135220385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341912703430892184360587693 128217263786584569135220385)
        ·
          refine ⟨96162947839938426851415289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128217263786584569135220385 96162947839938426851415289)
          ·
            refine ⟨72122210879953820138561467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96162947839938426851415289 72122210879953820138561467)
            ·
              refine ⟨108183316319930730207842201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72122210879953820138561467 108183316319930730207842201)
              ·
                refine ⟨81137487239948047655881651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108183316319930730207842201 81137487239948047655881651)
                ·
                  refine ⟨121706230859922071483822477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81137487239948047655881651 121706230859922071483822477)
                  ·
                    refine ⟨45639836572470776806433429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121706230859922071483822477 45639836572470776806433429)
                    ·
                      refine ⟨2139367339334567662801567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45639836572470776806433429 2139367339334567662801567)
                      ·
                        rfl

theorem cell23_4166403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_4166403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166403 prefixEnd_4166403 := by exact prefixLift 4166403
  have htrace : WordTrace (prefixWord ++ tailWord_4166403) baseStart_4166403 baseEnd_4166403 := by
    simpa [prefixWord, tailWord_4166403, baseEnd_4166403] using wordTrace_append hprefix tailTrace_4166403
  have hstable : (prefixWord ++ tailWord_4166403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166403).length < 2 ^ (prefixWord ++ tailWord_4166403).sum := by decide
  have hdescent : baseEnd_4166403 < baseStart_4166403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166407 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4166407 : Nat := 118140960795 + 4166407 * 2 ^ 59
def prefixEnd_4166407 : Nat := 4983230072969 + 3 ^ 40 * 4166407 * 2
def baseEnd_4166407 : Nat := 2139369393257185647151549

theorem tailTrace_4166407 : CollatzResearch.WordTrace tailWord_4166407 prefixEnd_4166407 2139369393257185647151549 := by
  unfold tailWord_4166407
  simp only [CollatzResearch.WordTrace]
  refine ⟨151961347416826479510073475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101307564944550986340048983 151961347416826479510073475)
  ·
    refine ⟨227942021125239719265110213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151961347416826479510073475 227942021125239719265110213)
    ·
      refine ⟨42739128960982447362208165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227942021125239719265110213 42739128960982447362208165)
      ·
        refine ⟨8013586680184208880414031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42739128960982447362208165 8013586680184208880414031)
        ·
          refine ⟨12020380020276313320621047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8013586680184208880414031 12020380020276313320621047)
          ·
            refine ⟨18030570030414469980931571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12020380020276313320621047 18030570030414469980931571)
            ·
              refine ⟨27045855045621704971397357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18030570030414469980931571 27045855045621704971397357)
              ·
                refine ⟨10142195642108139364274009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27045855045621704971397357 10142195642108139364274009)
                ·
                  refine ⟨7606646731581104523205507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10142195642108139364274009 7606646731581104523205507)
                  ·
                    refine ⟨11409970097371656784808261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7606646731581104523205507 11409970097371656784808261)
                    ·
                      refine ⟨2139369393257185647151549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11409970097371656784808261 2139369393257185647151549)
                      ·
                        rfl

theorem cell23_4166407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4166407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166407 prefixEnd_4166407 := by exact prefixLift 4166407
  have htrace : WordTrace (prefixWord ++ tailWord_4166407) baseStart_4166407 baseEnd_4166407 := by
    simpa [prefixWord, tailWord_4166407, baseEnd_4166407] using wordTrace_append hprefix tailTrace_4166407
  have hstable : (prefixWord ++ tailWord_4166407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166407).length < 2 ^ (prefixWord ++ tailWord_4166407).sum := by decide
  have hdescent : baseEnd_4166407 < baseStart_4166407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166443 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 2, 9]
def baseStart_4166443 : Nat := 118140960795 + 4166443 * 2 ^ 59
def prefixEnd_4166443 : Nat := 4983230072969 + 3 ^ 40 * 4166443 * 2
def baseEnd_4166443 : Nat := 713129292853582502100461

theorem tailTrace_4166443 : CollatzResearch.WordTrace tailWord_4166443 prefixEnd_4166443 713129292853582502100461 := by
  unfold tailWord_4166443
  simp only [CollatzResearch.WordTrace]
  refine ⟨151962660444696057658383983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101308440296464038438922655 151962660444696057658383983)
  ·
    refine ⟨227943990667044086487575975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151962660444696057658383983 227943990667044086487575975)
    ·
      refine ⟨341915986000566129731363963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227943990667044086487575975 341915986000566129731363963)
      ·
        refine ⟨512873979000849194597045945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341915986000566129731363963 512873979000849194597045945)
        ·
          refine ⟨384655484250636895947784459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512873979000849194597045945 384655484250636895947784459)
          ·
            refine ⟨576983226375955343921676689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384655484250636895947784459 576983226375955343921676689)
            ·
              refine ⟨432737419781966507941257517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576983226375955343921676689 432737419781966507941257517)
              ·
                refine ⟨162276532418237440477971569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 432737419781966507941257517 162276532418237440477971569)
                ·
                  refine ⟨121707399313678080358478677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162276532418237440477971569 121707399313678080358478677)
                  ·
                    refine ⟨713129292853582502100461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 121707399313678080358478677 713129292853582502100461)
                    ·
                      rfl

theorem cell23_4166443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 9].length) (baseStart_4166443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166443 prefixEnd_4166443 := by exact prefixLift 4166443
  have htrace : WordTrace (prefixWord ++ tailWord_4166443) baseStart_4166443 baseEnd_4166443 := by
    simpa [prefixWord, tailWord_4166443, baseEnd_4166443] using wordTrace_append hprefix tailTrace_4166443
  have hstable : (prefixWord ++ tailWord_4166443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166443).length < 2 ^ (prefixWord ++ tailWord_4166443).sum := by decide
  have hdescent : baseEnd_4166443 < baseStart_4166443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166461 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_4166461 : Nat := 118140960795 + 4166461 * 2 ^ 59
def prefixEnd_4166461 : Nat := 4983230072969 + 3 ^ 40 * 4166461 * 2
def baseEnd_4166461 : Nat := 2139397121212528435876301

theorem tailTrace_4166461 : CollatzResearch.WordTrace tailWord_4166461 prefixEnd_4166461 2139397121212528435876301 := by
  unfold tailWord_4166461
  simp only [CollatzResearch.WordTrace]
  refine ⟨151963316958630846732539237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101308877972420564488359491 151963316958630846732539237)
  ·
    refine ⟨28493121929743283762351107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151963316958630846732539237 28493121929743283762351107)
    ·
      refine ⟨42739682894614925643526661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28493121929743283762351107 42739682894614925643526661)
      ·
        refine ⟨8013690542740298558161249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42739682894614925643526661 8013690542740298558161249)
        ·
          refine ⟨6010267907055223918620937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8013690542740298558161249 6010267907055223918620937)
          ·
            refine ⟨4507700930291417938965703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6010267907055223918620937 4507700930291417938965703)
            ·
              refine ⟨6761551395437126908448555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507700930291417938965703 6761551395437126908448555)
              ·
                refine ⟨10142327093155690362672833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761551395437126908448555 10142327093155690362672833)
                ·
                  refine ⟨7606745319866767772004625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10142327093155690362672833 7606745319866767772004625)
                  ·
                    refine ⟨5705058989900075829003469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606745319866767772004625 5705058989900075829003469)
                    ·
                      refine ⟨2139397121212528435876301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5705058989900075829003469 2139397121212528435876301)
                      ·
                        rfl

theorem cell23_4166461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_4166461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166461 prefixEnd_4166461 := by exact prefixLift 4166461
  have htrace : WordTrace (prefixWord ++ tailWord_4166461) baseStart_4166461 baseEnd_4166461 := by
    simpa [prefixWord, tailWord_4166461, baseEnd_4166461] using wordTrace_append hprefix tailTrace_4166461
  have hstable : (prefixWord ++ tailWord_4166461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166461).length < 2 ^ (prefixWord ++ tailWord_4166461).sum := by decide
  have hdescent : baseEnd_4166461 < baseStart_4166461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166467 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 1, 5, 2]
def baseStart_4166467 : Nat := 118140960795 + 4166467 * 2 ^ 59
def prefixEnd_4166467 : Nat := 4983230072969 + 3 ^ 40 * 4166467 * 2
def baseEnd_4166467 : Nat := 2139400202096455412401273

theorem tailTrace_4166467 : CollatzResearch.WordTrace tailWord_4166467 prefixEnd_4166467 2139400202096455412401273 := by
  unfold tailWord_4166467
  simp only [CollatzResearch.WordTrace]
  refine ⟨151963535796609109757257655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101309023864406073171505103 151963535796609109757257655)
  ·
    refine ⟨227945303694913664635886483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151963535796609109757257655 227945303694913664635886483)
    ·
      refine ⟨341917955542370496953829725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227945303694913664635886483 341917955542370496953829725)
      ·
        refine ⟨128219233328388936357686147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341917955542370496953829725 128219233328388936357686147)
        ·
          refine ⟨192328849992583404536529221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128219233328388936357686147 192328849992583404536529221)
          ·
            refine ⟨36061659373609388350599229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192328849992583404536529221 36061659373609388350599229)
            ·
              refine ⟨13523122265103520631474711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36061659373609388350599229 13523122265103520631474711)
              ·
                refine ⟨20284683397655280947212067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13523122265103520631474711 20284683397655280947212067)
                ·
                  refine ⟨30427025096482921420818101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20284683397655280947212067 30427025096482921420818101)
                  ·
                    refine ⟨2852533602795273883201697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30427025096482921420818101 2852533602795273883201697)
                    ·
                      refine ⟨2139400202096455412401273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852533602795273883201697 2139400202096455412401273)
                      ·
                        rfl

theorem cell23_4166467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_4166467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166467 prefixEnd_4166467 := by exact prefixLift 4166467
  have htrace : WordTrace (prefixWord ++ tailWord_4166467) baseStart_4166467 baseEnd_4166467 := by
    simpa [prefixWord, tailWord_4166467, baseEnd_4166467] using wordTrace_append hprefix tailTrace_4166467
  have hstable : (prefixWord ++ tailWord_4166467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166467).length < 2 ^ (prefixWord ++ tailWord_4166467).sum := by decide
  have hdescent : baseEnd_4166467 < baseStart_4166467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166507 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 2, 4]
def baseStart_4166507 : Nat := 118140960795 + 4166507 * 2 ^ 59
def prefixEnd_4166507 : Nat := 4983230072969 + 3 ^ 40 * 4166507 * 2
def baseEnd_4166507 : Nat := 713140247107545085300363

theorem tailTrace_4166507 : CollatzResearch.WordTrace tailWord_4166507 prefixEnd_4166507 713140247107545085300363 := by
  unfold tailWord_4166507
  simp only [CollatzResearch.WordTrace]
  refine ⟨151964994716464196588713775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101309996477642797725809183 151964994716464196588713775)
  ·
    refine ⟨227947492074696294883070663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151964994716464196588713775 227947492074696294883070663)
    ·
      refine ⟨341921238112044442324605995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227947492074696294883070663 341921238112044442324605995)
      ·
        refine ⟨512881857168066663486908993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341921238112044442324605995 512881857168066663486908993)
        ·
          refine ⟨384661392876049997615181745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512881857168066663486908993 384661392876049997615181745)
          ·
            refine ⟨288496044657037498211386309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384661392876049997615181745 288496044657037498211386309)
            ·
              refine ⟨54093008373194530914634933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288496044657037498211386309 54093008373194530914634933)
              ·
                refine ⟨5071219534986987273247025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54093008373194530914634933 5071219534986987273247025)
                ·
                  refine ⟨3803414651240240454935269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5071219534986987273247025 3803414651240240454935269)
                  ·
                    refine ⟨713140247107545085300363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803414651240240454935269 713140247107545085300363)
                    ·
                      rfl

theorem cell23_4166507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 4].length) (baseStart_4166507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166507 prefixEnd_4166507 := by exact prefixLift 4166507
  have htrace : WordTrace (prefixWord ++ tailWord_4166507) baseStart_4166507 baseEnd_4166507 := by
    simpa [prefixWord, tailWord_4166507, baseEnd_4166507] using wordTrace_append hprefix tailTrace_4166507
  have hstable : (prefixWord ++ tailWord_4166507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166507).length < 2 ^ (prefixWord ++ tailWord_4166507).sum := by decide
  have hdescent : baseEnd_4166507 < baseStart_4166507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166582 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4166582 : Nat := 118140960795 + 4166582 * 2 ^ 59
def prefixEnd_4166582 : Nat := 4983230072969 + 3 ^ 40 * 4166582 * 2
def baseEnd_4166582 : Nat := 2139459252371722462463245

theorem tailTrace_4166582 : CollatzResearch.WordTrace tailWord_4166582 prefixEnd_4166582 2139459252371722462463245 := by
  unfold tailWord_4166582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9497983136949530274855875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101311820127461656265129333 9497983136949530274855875)
  ·
    refine ⟨14246974705424295412283813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9497983136949530274855875 14246974705424295412283813)
    ·
      refine ⟨2671307757267055389803215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14246974705424295412283813 2671307757267055389803215)
      ·
        refine ⟨4006961635900583084704823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671307757267055389803215 4006961635900583084704823)
        ·
          refine ⟨6010442453850874627057235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4006961635900583084704823 6010442453850874627057235)
          ·
            refine ⟨9015663680776311940585853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6010442453850874627057235 9015663680776311940585853)
            ·
              refine ⟨3380873880291116977719695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9015663680776311940585853 3380873880291116977719695)
              ·
                refine ⟨5071310820436675466579543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380873880291116977719695 5071310820436675466579543)
                ·
                  refine ⟨7606966230655013199869315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071310820436675466579543 7606966230655013199869315)
                  ·
                    refine ⟨11410449345982519799803973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7606966230655013199869315 11410449345982519799803973)
                    ·
                      refine ⟨2139459252371722462463245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11410449345982519799803973 2139459252371722462463245)
                      ·
                        rfl

theorem cell23_4166582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4166582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166582 prefixEnd_4166582 := by exact prefixLift 4166582
  have htrace : WordTrace (prefixWord ++ tailWord_4166582) baseStart_4166582 baseEnd_4166582 := by
    simpa [prefixWord, tailWord_4166582, baseEnd_4166582] using wordTrace_append hprefix tailTrace_4166582
  have hstable : (prefixWord ++ tailWord_4166582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166582).length < 2 ^ (prefixWord ++ tailWord_4166582).sum := by decide
  have hdescent : baseEnd_4166582 < baseStart_4166582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166587 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 2, 8, 2]
def baseStart_4166587 : Nat := 118140960795 + 4166587 * 2 ^ 59
def prefixEnd_4166587 : Nat := 4983230072969 + 3 ^ 40 * 4166587 * 2
def baseEnd_4166587 : Nat := 2139461819774994942900721

theorem tailTrace_4166587 : CollatzResearch.WordTrace tailWord_4166587 prefixEnd_4166587 2139461819774994942900721 := by
  unfold tailWord_4166587
  simp only [CollatzResearch.WordTrace]
  refine ⟨151967912556174370251626015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101311941704116246834417343 151967912556174370251626015)
  ·
    refine ⟨227951868834261555377439023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151967912556174370251626015 227951868834261555377439023)
    ·
      refine ⟨341927803251392333066158535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227951868834261555377439023 341927803251392333066158535)
      ·
        refine ⟨512891704877088499599237803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341927803251392333066158535 512891704877088499599237803)
        ·
          refine ⟨769337557315632749398856705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512891704877088499599237803 769337557315632749398856705)
          ·
            refine ⟨577003167986724562049142529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769337557315632749398856705 577003167986724562049142529)
            ·
              refine ⟨432752375990043421536856897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577003167986724562049142529 432752375990043421536856897)
              ·
                refine ⟨324564281992532566152642673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432752375990043421536856897 324564281992532566152642673)
                ·
                  refine ⟨243423211494399424614482005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324564281992532566152642673 243423211494399424614482005)
                  ·
                    refine ⟨2852615759699993257200961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 243423211494399424614482005 2852615759699993257200961)
                    ·
                      refine ⟨2139461819774994942900721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852615759699993257200961 2139461819774994942900721)
                      ·
                        rfl

theorem cell23_4166587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 8, 2].length) (baseStart_4166587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166587 prefixEnd_4166587 := by exact prefixLift 4166587
  have htrace : WordTrace (prefixWord ++ tailWord_4166587) baseStart_4166587 baseEnd_4166587 := by
    simpa [prefixWord, tailWord_4166587, baseEnd_4166587] using wordTrace_append hprefix tailTrace_4166587
  have hstable : (prefixWord ++ tailWord_4166587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166587).length < 2 ^ (prefixWord ++ tailWord_4166587).sum := by decide
  have hdescent : baseEnd_4166587 < baseStart_4166587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166604 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 3, 4, 2]
def baseStart_4166604 : Nat := 118140960795 + 4166604 * 2 ^ 59
def prefixEnd_4166604 : Nat := 4983230072969 + 3 ^ 40 * 4166604 * 2
def baseEnd_4166604 : Nat := 2139470548946121376388143

theorem tailTrace_4166604 : CollatzResearch.WordTrace tailWord_4166604 prefixEnd_4166604 2139470548946121376388143 := by
  unfold tailWord_4166604
  simp only [CollatzResearch.WordTrace]
  refine ⟨75984266298556391077497433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101312355064741854769996577 75984266298556391077497433)
  ·
    refine ⟨56988199723917293308123075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75984266298556391077497433 56988199723917293308123075)
    ·
      refine ⟨85482299585875939962184613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56988199723917293308123075 85482299585875939962184613)
      ·
        refine ⟨16027931172351738742909615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85482299585875939962184613 16027931172351738742909615)
        ·
          refine ⟨24041896758527608114364423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16027931172351738742909615 24041896758527608114364423)
          ·
            refine ⟨36062845137791412171546635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24041896758527608114364423 36062845137791412171546635)
            ·
              refine ⟨54094267706687118257319953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36062845137791412171546635 54094267706687118257319953)
              ·
                refine ⟨40570700780015338692989965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54094267706687118257319953 40570700780015338692989965)
                ·
                  refine ⟨15214012792505752009871237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40570700780015338692989965 15214012792505752009871237)
                  ·
                    refine ⟨2852627398594828501850857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15214012792505752009871237 2852627398594828501850857)
                    ·
                      refine ⟨2139470548946121376388143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852627398594828501850857 2139470548946121376388143)
                      ·
                        rfl

theorem cell23_4166604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_4166604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166604 prefixEnd_4166604 := by exact prefixLift 4166604
  have htrace : WordTrace (prefixWord ++ tailWord_4166604) baseStart_4166604 baseEnd_4166604 := by
    simpa [prefixWord, tailWord_4166604, baseEnd_4166604] using wordTrace_append hprefix tailTrace_4166604
  have hstable : (prefixWord ++ tailWord_4166604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166604).length < 2 ^ (prefixWord ++ tailWord_4166604).sum := by decide
  have hdescent : baseEnd_4166604 < baseStart_4166604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166605 : List Nat := [1, 6, 3, 1, 2, 1, 1, 8]
def baseStart_4166605 : Nat := 118140960795 + 4166605 * 2 ^ 59
def prefixEnd_4166605 : Nat := 4983230072969 + 3 ^ 40 * 4166605 * 2
def baseEnd_4166605 : Nat := 79239668978769476758357

theorem tailTrace_4166605 : CollatzResearch.WordTrace tailWord_4166605 prefixEnd_4166605 79239668978769476758357 := by
  unfold tailWord_4166605
  simp only [CollatzResearch.WordTrace]
  refine ⟨151968569070109159325781269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101312379380072772883854179 151968569070109159325781269)
  ·
    refine ⟨7123526675161366843395997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151968569070109159325781269 7123526675161366843395997)
    ·
      refine ⟨2671322503185512566273499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7123526675161366843395997 2671322503185512566273499)
      ·
        refine ⟨4006983754778268849410249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671322503185512566273499 4006983754778268849410249)
        ·
          refine ⟨3005237816083701637057687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4006983754778268849410249 3005237816083701637057687)
          ·
            refine ⟨4507856724125552455586531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005237816083701637057687 4507856724125552455586531)
            ·
              refine ⟨6761785086188328683379797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507856724125552455586531 6761785086188328683379797)
              ·
                refine ⟨79239668978769476758357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6761785086188328683379797 79239668978769476758357)
                ·
                  rfl

theorem cell23_4166605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 8].length) (baseStart_4166605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166605 prefixEnd_4166605 := by exact prefixLift 4166605
  have htrace : WordTrace (prefixWord ++ tailWord_4166605) baseStart_4166605 baseEnd_4166605 := by
    simpa [prefixWord, tailWord_4166605, baseEnd_4166605] using wordTrace_append hprefix tailTrace_4166605
  have hstable : (prefixWord ++ tailWord_4166605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166605).length < 2 ^ (prefixWord ++ tailWord_4166605).sum := by decide
  have hdescent : baseEnd_4166605 < baseStart_4166605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166607 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 3]
def baseStart_4166607 : Nat := 118140960795 + 4166607 * 2 ^ 59
def prefixEnd_4166607 : Nat := 4983230072969 + 3 ^ 40 * 4166607 * 2
def baseEnd_4166607 : Nat := 2139472089388084864650629

theorem tailTrace_4166607 : CollatzResearch.WordTrace tailWord_4166607 prefixEnd_4166607 2139472089388084864650629 := by
  unfold tailWord_4166607
  simp only [CollatzResearch.WordTrace]
  refine ⟨151968642016101913667354075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101312428010734609111569383 151968642016101913667354075)
  ·
    refine ⟨227952963024152870501031113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151968642016101913667354075 227952963024152870501031113)
    ·
      refine ⟨170964722268114652875773335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227952963024152870501031113 170964722268114652875773335)
      ·
        refine ⟨256447083402171979313660003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170964722268114652875773335 256447083402171979313660003)
        ·
          refine ⟨384670625103257968970490005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256447083402171979313660003 384670625103257968970490005)
          ·
            refine ⟨18031435551715217295491719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 384670625103257968970490005 18031435551715217295491719)
            ·
              refine ⟨27047153327572825943237579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18031435551715217295491719 27047153327572825943237579)
              ·
                refine ⟨40570729991359238914856369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27047153327572825943237579 40570729991359238914856369)
                ·
                  refine ⟨30428047493519429186142277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40570729991359238914856369 30428047493519429186142277)
                  ·
                    refine ⟨5705258905034892972401677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30428047493519429186142277 5705258905034892972401677)
                    ·
                      refine ⟨2139472089388084864650629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5705258905034892972401677 2139472089388084864650629)
                      ·
                        rfl

theorem cell23_4166607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 4, 3].length) (baseStart_4166607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166607 prefixEnd_4166607 := by exact prefixLift 4166607
  have htrace : WordTrace (prefixWord ++ tailWord_4166607) baseStart_4166607 baseEnd_4166607 := by
    simpa [prefixWord, tailWord_4166607, baseEnd_4166607] using wordTrace_append hprefix tailTrace_4166607
  have hstable : (prefixWord ++ tailWord_4166607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166607).length < 2 ^ (prefixWord ++ tailWord_4166607).sum := by decide
  have hdescent : baseEnd_4166607 < baseStart_4166607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166614 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4166614 : Nat := 118140960795 + 4166614 * 2 ^ 59
def prefixEnd_4166614 : Nat := 4983230072969 + 3 ^ 40 * 4166614 * 2
def baseEnd_4166614 : Nat := 713158561250888779087699

theorem tailTrace_4166614 : CollatzResearch.WordTrace tailWord_4166614 prefixEnd_4166614 713158561250888779087699 := by
  unfold tailWord_4166614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9498056082942284616428681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101312598218051035908572597 9498056082942284616428681)
  ·
    refine ⟨7123542062206713462321511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9498056082942284616428681 7123542062206713462321511)
    ·
      refine ⟨10685313093310070193482267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7123542062206713462321511 10685313093310070193482267)
      ·
        refine ⟨16027969639965105290223401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10685313093310070193482267 16027969639965105290223401)
        ·
          refine ⟨12020977229973828967667551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16027969639965105290223401 12020977229973828967667551)
          ·
            refine ⟨18031465844960743451501327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12020977229973828967667551 18031465844960743451501327)
            ·
              refine ⟨27047198767441115177251991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18031465844960743451501327 27047198767441115177251991)
              ·
                refine ⟨40570798151161672765877987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27047198767441115177251991 40570798151161672765877987)
                ·
                  refine ⟨60856197226742509148816981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40570798151161672765877987 60856197226742509148816981)
                  ·
                    refine ⟨713158561250888779087699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60856197226742509148816981 713158561250888779087699)
                    ·
                      rfl

theorem cell23_4166614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4166614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166614 prefixEnd_4166614 := by exact prefixLift 4166614
  have htrace : WordTrace (prefixWord ++ tailWord_4166614) baseStart_4166614 baseEnd_4166614 := by
    simpa [prefixWord, tailWord_4166614, baseEnd_4166614] using wordTrace_append hprefix tailTrace_4166614
  have hstable : (prefixWord ++ tailWord_4166614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166614).length < 2 ^ (prefixWord ++ tailWord_4166614).sum := by decide
  have hdescent : baseEnd_4166614 < baseStart_4166614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166617 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_4166617 : Nat := 118140960795 + 4166617 * 2 ^ 59
def prefixEnd_4166617 : Nat := 4983230072969 + 3 ^ 40 * 4166617 * 2
def baseEnd_4166617 : Nat := 2139477224194629825525583

theorem tailTrace_4166617 : CollatzResearch.WordTrace tailWord_4166617 prefixEnd_4166617 2139477224194629825525583 := by
  unfold tailWord_4166617
  simp only [CollatzResearch.WordTrace]
  refine ⟨151969006746065685375218105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101312671164043790250145403 151969006746065685375218105)
  ·
    refine ⟨113976755059549264031413579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151969006746065685375218105 113976755059549264031413579)
    ·
      refine ⟨170965132589323896047120369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113976755059549264031413579 170965132589323896047120369)
      ·
        refine ⟨128223849441992922035340277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170965132589323896047120369 128223849441992922035340277)
        ·
          refine ⟨12020985885186836440813151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128223849441992922035340277 12020985885186836440813151)
          ·
            refine ⟨18031478827780254661219727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12020985885186836440813151 18031478827780254661219727)
            ·
              refine ⟨27047218241670381991829591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18031478827780254661219727 27047218241670381991829591)
              ·
                refine ⟨40570827362505572987744387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27047218241670381991829591 40570827362505572987744387)
                ·
                  refine ⟨60856241043758359481616581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40570827362505572987744387 60856241043758359481616581)
                  ·
                    refine ⟨11410545195704692402803109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60856241043758359481616581 11410545195704692402803109)
                    ·
                      refine ⟨2139477224194629825525583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11410545195704692402803109 2139477224194629825525583)
                      ·
                        rfl

theorem cell23_4166617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_4166617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166617 prefixEnd_4166617 := by exact prefixLift 4166617
  have htrace : WordTrace (prefixWord ++ tailWord_4166617) baseStart_4166617 baseEnd_4166617 := by
    simpa [prefixWord, tailWord_4166617, baseEnd_4166617] using wordTrace_append hprefix tailTrace_4166617
  have hstable : (prefixWord ++ tailWord_4166617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166617).length < 2 ^ (prefixWord ++ tailWord_4166617).sum := by decide
  have hdescent : baseEnd_4166617 < baseStart_4166617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166621 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_4166621 : Nat := 118140960795 + 4166621 * 2 ^ 59
def prefixEnd_4166621 : Nat := 4983230072969 + 3 ^ 40 * 4166621 * 2
def baseEnd_4166621 : Nat := 2139479278117247809875565

theorem tailTrace_4166621 : CollatzResearch.WordTrace tailWord_4166621 prefixEnd_4166621 2139479278117247809875565 := by
  unfold tailWord_4166621
  simp only [CollatzResearch.WordTrace]
  refine ⟨151969152638051194058363717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101312768425367462705575811 151969152638051194058363717)
  ·
    refine ⟨28494216119634598885943197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151969152638051194058363717 28494216119634598885943197)
    ·
      refine ⟨10685331044862974582228699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28494216119634598885943197 10685331044862974582228699)
      ·
        refine ⟨16027996567294461873343049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10685331044862974582228699 16027996567294461873343049)
        ·
          refine ⟨12020997425470846405007287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16027996567294461873343049 12020997425470846405007287)
          ·
            refine ⟨18031496138206269607510931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12020997425470846405007287 18031496138206269607510931)
            ·
              refine ⟨27047244207309404411266397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18031496138206269607510931 27047244207309404411266397)
              ·
                refine ⟨10142716577741026654224899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27047244207309404411266397 10142716577741026654224899)
                ·
                  refine ⟨15214074866611539981337349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10142716577741026654224899 15214074866611539981337349)
                  ·
                    refine ⟨2852639037489663746500753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15214074866611539981337349 2852639037489663746500753)
                    ·
                      refine ⟨2139479278117247809875565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852639037489663746500753 2139479278117247809875565)
                      ·
                        rfl

theorem cell23_4166621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_4166621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166621 prefixEnd_4166621 := by exact prefixLift 4166621
  have htrace : WordTrace (prefixWord ++ tailWord_4166621) baseStart_4166621 baseEnd_4166621 := by
    simpa [prefixWord, tailWord_4166621, baseEnd_4166621] using wordTrace_append hprefix tailTrace_4166621
  have hstable : (prefixWord ++ tailWord_4166621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166621).length < 2 ^ (prefixWord ++ tailWord_4166621).sum := by decide
  have hdescent : baseEnd_4166621 < baseStart_4166621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166627 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 7]
def baseStart_4166627 : Nat := 118140960795 + 4166627 * 2 ^ 59
def prefixEnd_4166627 : Nat := 4983230072969 + 3 ^ 40 * 4166627 * 2
def baseEnd_4166627 : Nat := 237720262111241642933393

theorem tailTrace_4166627 : CollatzResearch.WordTrace tailWord_4166627 prefixEnd_4166627 237720262111241642933393 := by
  unfold tailWord_4166627
  simp only [CollatzResearch.WordTrace]
  refine ⟨151969371476029457083082135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101312914317352971388721423 151969371476029457083082135)
  ·
    refine ⟨227954057214044185624623203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151969371476029457083082135 227954057214044185624623203)
    ·
      refine ⟨341931085821066278436934805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227954057214044185624623203 341931085821066278436934805)
      ·
        refine ⟨16028019647862481801731319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 341931085821066278436934805 16028019647862481801731319)
        ·
          refine ⟨24042029471793722702596979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16028019647862481801731319 24042029471793722702596979)
          ·
            refine ⟨36063044207690584053895469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24042029471793722702596979 36063044207690584053895469)
            ·
              refine ⟨13523641577883969020210801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36063044207690584053895469 13523641577883969020210801)
              ·
                refine ⟨10142731183412976765158101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13523641577883969020210801 10142731183412976765158101)
                ·
                  refine ⟨237720262111241642933393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10142731183412976765158101 237720262111241642933393)
                  ·
                    rfl

theorem cell23_4166627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 7].length) (baseStart_4166627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166627 prefixEnd_4166627 := by exact prefixLift 4166627
  have htrace : WordTrace (prefixWord ++ tailWord_4166627) baseStart_4166627 baseEnd_4166627 := by
    simpa [prefixWord, tailWord_4166627, baseEnd_4166627] using wordTrace_append hprefix tailTrace_4166627
  have hstable : (prefixWord ++ tailWord_4166627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166627).length < 2 ^ (prefixWord ++ tailWord_4166627).sum := by decide
  have hdescent : baseEnd_4166627 < baseStart_4166627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166642 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4166642 : Nat := 118140960795 + 4166642 * 2 ^ 59
def prefixEnd_4166642 : Nat := 4983230072969 + 3 ^ 40 * 4166642 * 2
def baseEnd_4166642 : Nat := 2139490061210992227712969

theorem tailTrace_4166642 : CollatzResearch.WordTrace tailWord_4166642 prefixEnd_4166642 2139490061210992227712969 := by
  unfold tailWord_4166642
  simp only [CollatzResearch.WordTrace]
  refine ⟨37992479642743778661219545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101313279047316743096585453 37992479642743778661219545)
  ·
    refine ⟨28494359732057833995914659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37992479642743778661219545 28494359732057833995914659)
    ·
      refine ⟨42741539598086750993871989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28494359732057833995914659 42741539598086750993871989)
      ·
        refine ⟨4007019337320632905675499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42741539598086750993871989 4007019337320632905675499)
        ·
          refine ⟨6010529005980949358513249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007019337320632905675499 6010529005980949358513249)
          ·
            refine ⟨4507896754485712018884937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6010529005980949358513249 4507896754485712018884937)
            ·
              refine ⟨3380922565864284014163703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4507896754485712018884937 3380922565864284014163703)
              ·
                refine ⟨5071383848796426021245555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3380922565864284014163703 5071383848796426021245555)
                ·
                  refine ⟨7607075773194639031868333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071383848796426021245555 7607075773194639031868333)
                  ·
                    refine ⟨2852653414947989636950625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7607075773194639031868333 2852653414947989636950625)
                    ·
                      refine ⟨2139490061210992227712969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852653414947989636950625 2139490061210992227712969)
                      ·
                        rfl

theorem cell23_4166642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4166642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166642 prefixEnd_4166642 := by exact prefixLift 4166642
  have htrace : WordTrace (prefixWord ++ tailWord_4166642) baseStart_4166642 baseEnd_4166642 := by
    simpa [prefixWord, tailWord_4166642, baseEnd_4166642] using wordTrace_append hprefix tailTrace_4166642
  have hstable : (prefixWord ++ tailWord_4166642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166642).length < 2 ^ (prefixWord ++ tailWord_4166642).sum := by decide
  have hdescent : baseEnd_4166642 < baseStart_4166642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166714 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_4166714 : Nat := 118140960795 + 4166714 * 2 ^ 59
def prefixEnd_4166714 : Nat := 4983230072969 + 3 ^ 40 * 4166714 * 2
def baseEnd_4166714 : Nat := 2139527031818115946012637

theorem tailTrace_4166714 : CollatzResearch.WordTrace tailWord_4166714 prefixEnd_4166714 2139527031818115946012637 := by
  unfold tailWord_4166714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37993136156678567735374799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101315029751142847294332797 37993136156678567735374799)
  ·
    refine ⟨56989704235017851603062199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37993136156678567735374799 56989704235017851603062199)
    ·
      refine ⟨85484556352526777404593299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56989704235017851603062199 85484556352526777404593299)
      ·
        refine ⟨128226834528790166106889949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85484556352526777404593299 128226834528790166106889949)
        ·
          refine ⟨48085062948296312290083731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128226834528790166106889949 48085062948296312290083731)
          ·
            refine ⟨72127594422444468435125597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48085062948296312290083731 72127594422444468435125597)
            ·
              refine ⟨27047847908416675663172099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72127594422444468435125597 27047847908416675663172099)
              ·
                refine ⟨40571771862625013494758149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27047847908416675663172099 40571771862625013494758149)
                ·
                  refine ⟨7607207224242190030267153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40571771862625013494758149 7607207224242190030267153)
                  ·
                    refine ⟨5705405418181642522700365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7607207224242190030267153 5705405418181642522700365)
                    ·
                      refine ⟨2139527031818115946012637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5705405418181642522700365 2139527031818115946012637)
                      ·
                        rfl

theorem cell23_4166714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_4166714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166714 prefixEnd_4166714 := by exact prefixLift 4166714
  have htrace : WordTrace (prefixWord ++ tailWord_4166714) baseStart_4166714 baseEnd_4166714 := by
    simpa [prefixWord, tailWord_4166714, baseEnd_4166714] using wordTrace_append hprefix tailTrace_4166714
  have hstable : (prefixWord ++ tailWord_4166714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166714).length < 2 ^ (prefixWord ++ tailWord_4166714).sum := by decide
  have hdescent : baseEnd_4166714 < baseStart_4166714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166734 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_4166734 : Nat := 118140960795 + 4166734 * 2 ^ 59
def prefixEnd_4166734 : Nat := 4983230072969 + 3 ^ 40 * 4166734 * 2
def baseEnd_4166734 : Nat := 237726366825689540862505

theorem tailTrace_4166734 : CollatzResearch.WordTrace tailWord_4166734 prefixEnd_4166734 237726366825689540862505 := by
  unfold tailWord_4166734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18996659260830226794653407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101315516057761209571484837 18996659260830226794653407)
  ·
    refine ⟨28494988891245340191980111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18996659260830226794653407 28494988891245340191980111)
    ·
      refine ⟨42742483336868010287970167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28494988891245340191980111 42742483336868010287970167)
      ·
        refine ⟨64113725005302015431955251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42742483336868010287970167 64113725005302015431955251)
        ·
          refine ⟨96170587507953023147932877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64113725005302015431955251 96170587507953023147932877)
          ·
            refine ⟨36063970315482383680474829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96170587507953023147932877 36063970315482383680474829)
            ·
              refine ⟨13523988868305893880178061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36063970315482383680474829 13523988868305893880178061)
              ·
                refine ⟨5071495825614710205066773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13523988868305893880178061 5071495825614710205066773)
                ·
                  refine ⟨237726366825689540862505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5071495825614710205066773 237726366825689540862505)
                  ·
                    rfl

theorem cell23_4166734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_4166734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166734 prefixEnd_4166734 := by exact prefixLift 4166734
  have htrace : WordTrace (prefixWord ++ tailWord_4166734) baseStart_4166734 baseEnd_4166734 := by
    simpa [prefixWord, tailWord_4166734, baseEnd_4166734] using wordTrace_append hprefix tailTrace_4166734
  have hstable : (prefixWord ++ tailWord_4166734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166734).length < 2 ^ (prefixWord ++ tailWord_4166734).sum := by decide
  have hdescent : baseEnd_4166734 < baseStart_4166734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166737 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_4166737 : Nat := 118140960795 + 4166737 * 2 ^ 59
def prefixEnd_4166737 : Nat := 4983230072969 + 3 ^ 40 * 4166737 * 2
def baseEnd_4166737 : Nat := 2139538841873169356025031

theorem tailTrace_4166737 : CollatzResearch.WordTrace tailWord_4166737 prefixEnd_4166737 2139538841873169356025031 := by
  unfold tailWord_4166737
  simp only [CollatzResearch.WordTrace]
  refine ⟨151973383505630945869586465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101315589003753963913057643 151973383505630945869586465)
  ·
    refine ⟨113980037629223209402189849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151973383505630945869586465 113980037629223209402189849)
    ·
      refine ⟨85485028221917407051642387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113980037629223209402189849 85485028221917407051642387)
      ·
        refine ⟨128227542332876110577463581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85485028221917407051642387 128227542332876110577463581)
        ·
          refine ⟨48085328374828541466548843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128227542332876110577463581 48085328374828541466548843)
          ·
            refine ⟨72127992562242812199823265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48085328374828541466548843 72127992562242812199823265)
            ·
              refine ⟨54095994421682109149867449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72127992562242812199823265 54095994421682109149867449)
              ·
                refine ⟨40571995816261581862400587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54095994421682109149867449 40571995816261581862400587)
                ·
                  refine ⟨60857993724392372793600881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40571995816261581862400587 60857993724392372793600881)
                  ·
                    refine ⟨45643495293294279595200661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60857993724392372793600881 45643495293294279595200661)
                    ·
                      refine ⟨2139538841873169356025031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45643495293294279595200661 2139538841873169356025031)
                      ·
                        rfl

theorem cell23_4166737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_4166737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166737 prefixEnd_4166737 := by exact prefixLift 4166737
  have htrace : WordTrace (prefixWord ++ tailWord_4166737) baseStart_4166737 baseEnd_4166737 := by
    simpa [prefixWord, tailWord_4166737, baseEnd_4166737] using wordTrace_append hprefix tailTrace_4166737
  have hstable : (prefixWord ++ tailWord_4166737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166737).length < 2 ^ (prefixWord ++ tailWord_4166737).sum := by decide
  have hdescent : baseEnd_4166737 < baseStart_4166737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166784 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_4166784 : Nat := 118140960795 + 4166784 * 2 ^ 59
def prefixEnd_4166784 : Nat := 4983230072969 + 3 ^ 40 * 4166784 * 2
def baseEnd_4166784 : Nat := 2139562975463930672137315

theorem tailTrace_4166784 : CollatzResearch.WordTrace tailWord_4166784 prefixEnd_4166784 2139562975463930672137315 := by
  unfold tailWord_4166784
  simp only [CollatzResearch.WordTrace]
  refine ⟨75987548868230336448273703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101316731824307115264364937 75987548868230336448273703)
  ·
    refine ⟨113981323302345504672410555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75987548868230336448273703 113981323302345504672410555)
    ·
      refine ⟨170971984953518257008615833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113981323302345504672410555 170971984953518257008615833)
      ·
        refine ⟨128228988715138692756461875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170971984953518257008615833 128228988715138692756461875)
        ·
          refine ⟨192343483072708039134692813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128228988715138692756461875 192343483072708039134692813)
          ·
            refine ⟨72128806152265514675509805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192343483072708039134692813 72128806152265514675509805)
            ·
              refine ⟨27048302307099568003316177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72128806152265514675509805 27048302307099568003316177)
              ·
                refine ⟨20286226730324676002487133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27048302307099568003316177 20286226730324676002487133)
                ·
                  refine ⟨7607335023871753500932675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20286226730324676002487133 7607335023871753500932675)
                  ·
                    refine ⟨11411002535807630251399013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7607335023871753500932675 11411002535807630251399013)
                    ·
                      refine ⟨2139562975463930672137315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11411002535807630251399013 2139562975463930672137315)
                      ·
                        rfl

theorem cell23_4166784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_4166784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166784 prefixEnd_4166784 := by exact prefixLift 4166784
  have htrace : WordTrace (prefixWord ++ tailWord_4166784) baseStart_4166784 baseEnd_4166784 := by
    simpa [prefixWord, tailWord_4166784, baseEnd_4166784] using wordTrace_append hprefix tailTrace_4166784
  have hstable : (prefixWord ++ tailWord_4166784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166784).length < 2 ^ (prefixWord ++ tailWord_4166784).sum := by decide
  have hdescent : baseEnd_4166784 < baseStart_4166784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166815 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 1, 5]
def baseStart_4166815 : Nat := 118140960795 + 4166815 * 2 ^ 59
def prefixEnd_4166815 : Nat := 4983230072969 + 3 ^ 40 * 4166815 * 2
def baseEnd_4166815 : Nat := 713192964454740016949891

theorem tailTrace_4166815 : CollatzResearch.WordTrace tailWord_4166815 prefixEnd_4166815 713192964454740016949891 := by
  unfold tailWord_4166815
  simp only [CollatzResearch.WordTrace]
  refine ⟨151976228399348365190925899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101317485599565576793950599 151976228399348365190925899)
  ·
    refine ⟨227964342599022547786388849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151976228399348365190925899 227964342599022547786388849)
    ·
      refine ⟨170973256949266910839791637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227964342599022547786388849 170973256949266910839791637)
      ·
        refine ⟨8014371419496886445615233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 170973256949266910839791637 8014371419496886445615233)
        ·
          refine ⟨6010778564622664834211425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8014371419496886445615233 6010778564622664834211425)
          ·
            refine ⟨4508083923466998625658569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6010778564622664834211425 4508083923466998625658569)
            ·
              refine ⟨3381062942600248969243927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508083923466998625658569 3381062942600248969243927)
              ·
                refine ⟨5071594413900373453865891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381062942600248969243927 5071594413900373453865891)
                ·
                  refine ⟨7607391620850560180798837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071594413900373453865891 7607391620850560180798837)
                  ·
                    refine ⟨713192964454740016949891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7607391620850560180798837 713192964454740016949891)
                    ·
                      rfl

theorem cell23_4166815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 1, 5].length) (baseStart_4166815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166815 prefixEnd_4166815 := by exact prefixLift 4166815
  have htrace : WordTrace (prefixWord ++ tailWord_4166815) baseStart_4166815 baseEnd_4166815 := by
    simpa [prefixWord, tailWord_4166815, baseEnd_4166815] using wordTrace_append hprefix tailTrace_4166815
  have hstable : (prefixWord ++ tailWord_4166815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166815).length < 2 ^ (prefixWord ++ tailWord_4166815).sum := by decide
  have hdescent : baseEnd_4166815 < baseStart_4166815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166835 : List Nat := [1, 1, 1, 2, 3, 2, 4, 4, 1, 2, 2]
def baseStart_4166835 : Nat := 118140960795 + 4166835 * 2 ^ 59
def prefixEnd_4166835 : Nat := 4983230072969 + 3 ^ 40 * 4166835 * 2
def baseEnd_4166835 : Nat := 2139589162977309972599581

theorem tailTrace_4166835 : CollatzResearch.WordTrace tailWord_4166835 prefixEnd_4166835 2139589162977309972599581 := by
  unfold tailWord_4166835
  simp only [CollatzResearch.WordTrace]
  refine ⟨151976957859275908606653959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101317971906183939071102639 151976957859275908606653959)
  ·
    refine ⟨227965436788913862909980939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151976957859275908606653959 227965436788913862909980939)
    ·
      refine ⟨341948155183370794364971409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227965436788913862909980939 341948155183370794364971409)
      ·
        refine ⟨256461116387528095773728557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341948155183370794364971409 256461116387528095773728557)
        ·
          refine ⟨96172918645323035915148209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256461116387528095773728557 96172918645323035915148209)
          ·
            refine ⟨72129688983992276936361157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96172918645323035915148209 72129688983992276936361157)
            ·
              refine ⟨13524316684498551925567717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72129688983992276936361157 13524316684498551925567717)
              ·
                refine ⟨2535809378343478486043947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13524316684498551925567717 2535809378343478486043947)
                ·
                  refine ⟨3803714067515217729065921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535809378343478486043947 3803714067515217729065921)
                  ·
                    refine ⟨2852785550636413296799441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3803714067515217729065921 2852785550636413296799441)
                    ·
                      refine ⟨2139589162977309972599581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852785550636413296799441 2139589162977309972599581)
                      ·
                        rfl

theorem cell23_4166835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 2, 2].length) (baseStart_4166835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166835 prefixEnd_4166835 := by exact prefixLift 4166835
  have htrace : WordTrace (prefixWord ++ tailWord_4166835) baseStart_4166835 baseEnd_4166835 := by
    simpa [prefixWord, tailWord_4166835, baseEnd_4166835] using wordTrace_append hprefix tailTrace_4166835
  have hstable : (prefixWord ++ tailWord_4166835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166835).length < 2 ^ (prefixWord ++ tailWord_4166835).sum := by decide
  have hdescent : baseEnd_4166835 < baseStart_4166835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166848 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 4]
def baseStart_4166848 : Nat := 118140960795 + 4166848 * 2 ^ 59
def prefixEnd_4166848 : Nat := 4983230072969 + 3 ^ 40 * 4166848 * 2
def baseEnd_4166848 : Nat := 2139595838225818421737021

theorem tailTrace_4166848 : CollatzResearch.WordTrace tailWord_4166848 prefixEnd_4166848 2139595838225818421737021 := by
  unfold tailWord_4166848
  simp only [CollatzResearch.WordTrace]
  refine ⟨75988716004114405913438599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101318288005485874551251465 75988716004114405913438599)
  ·
    refine ⟨113983074006171608870157899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75988716004114405913438599 113983074006171608870157899)
    ·
      refine ⟨170974611009257413305236849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113983074006171608870157899 170974611009257413305236849)
      ·
        refine ⟨128230958256943059978927637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170974611009257413305236849 128230958256943059978927637)
        ·
          refine ⟨6010826168294205936512233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128230958256943059978927637 6010826168294205936512233)
          ·
            refine ⟨4508119626220654452384175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6010826168294205936512233 4508119626220654452384175)
            ·
              refine ⟨6762179439330981678576263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508119626220654452384175 6762179439330981678576263)
              ·
                refine ⟨10143269158996472517864395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762179439330981678576263 10143269158996472517864395)
                ·
                  refine ⟨15214903738494708776796593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10143269158996472517864395 15214903738494708776796593)
                  ·
                    refine ⟨11411177803871031582597445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15214903738494708776796593 11411177803871031582597445)
                    ·
                      refine ⟨2139595838225818421737021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11411177803871031582597445 2139595838225818421737021)
                      ·
                        rfl

theorem cell23_4166848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_4166848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166848 prefixEnd_4166848 := by exact prefixLift 4166848
  have htrace : WordTrace (prefixWord ++ tailWord_4166848) baseStart_4166848 baseEnd_4166848 := by
    simpa [prefixWord, tailWord_4166848, baseEnd_4166848] using wordTrace_append hprefix tailTrace_4166848
  have hstable : (prefixWord ++ tailWord_4166848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166848).length < 2 ^ (prefixWord ++ tailWord_4166848).sum := by decide
  have hdescent : baseEnd_4166848 < baseStart_4166848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166869 : List Nat := [1, 3, 2, 4, 1, 3, 1, 3, 1, 2, 2]
def baseStart_4166869 : Nat := 118140960795 + 4166869 * 2 ^ 59
def prefixEnd_4166869 : Nat := 4983230072969 + 3 ^ 40 * 4166869 * 2
def baseEnd_4166869 : Nat := 2139606621319562839574425

theorem tailTrace_4166869 : CollatzResearch.WordTrace tailWord_4166869 prefixEnd_4166869 2139606621319562839574425 := by
  unfold tailWord_4166869
  simp only [CollatzResearch.WordTrace]
  refine ⟨151978197941152732413391661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101318798627435154942261107 151978197941152732413391661)
  ·
    refine ⟨56991824227932274655021873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151978197941152732413391661 56991824227932274655021873)
    ·
      refine ⟨42743868170949205991266405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56991824227932274655021873 42743868170949205991266405)
      ·
        refine ⟨8014475282052976123362451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42743868170949205991266405 8014475282052976123362451)
        ·
          refine ⟨12021712923079464185043677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8014475282052976123362451 12021712923079464185043677)
          ·
            refine ⟨4508142346154799069391379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12021712923079464185043677 4508142346154799069391379)
            ·
              refine ⟨6762213519232198604087069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508142346154799069391379 6762213519232198604087069)
              ·
                refine ⟨2535830069712074476532651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6762213519232198604087069 2535830069712074476532651)
                ·
                  refine ⟨3803745104568111714798977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535830069712074476532651 3803745104568111714798977)
                  ·
                    refine ⟨2852808828426083786099233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3803745104568111714798977 2852808828426083786099233)
                    ·
                      refine ⟨2139606621319562839574425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2852808828426083786099233 2139606621319562839574425)
                      ·
                        rfl

theorem cell23_4166869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_4166869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166869 prefixEnd_4166869 := by exact prefixLift 4166869
  have htrace : WordTrace (prefixWord ++ tailWord_4166869) baseStart_4166869 baseEnd_4166869 := by
    simpa [prefixWord, tailWord_4166869, baseEnd_4166869] using wordTrace_append hprefix tailTrace_4166869
  have hstable : (prefixWord ++ tailWord_4166869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166869).length < 2 ^ (prefixWord ++ tailWord_4166869).sum := by decide
  have hdescent : baseEnd_4166869 < baseStart_4166869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166874 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_4166874 : Nat := 118140960795 + 4166874 * 2 ^ 59
def prefixEnd_4166874 : Nat := 4983230072969 + 3 ^ 40 * 4166874 * 2
def baseEnd_4166874 : Nat := 2139609188722835320011901

theorem tailTrace_4166874 : CollatzResearch.WordTrace tailWord_4166874 prefixEnd_4166874 2139609188722835320011901 := by
  unfold tailWord_4166874
  simp only [CollatzResearch.WordTrace]
  refine ⟨37994595076533654566830919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101318920204089745511549117 37994595076533654566830919)
  ·
    refine ⟨56991892614800481850246379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37994595076533654566830919 56991892614800481850246379)
    ·
      refine ⟨85487838922200722775369569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56991892614800481850246379 85487838922200722775369569)
      ·
        refine ⟨64115879191650542081527177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85487838922200722775369569 64115879191650542081527177)
        ·
          refine ⟨48086909393737906561145383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64115879191650542081527177 48086909393737906561145383)
          ·
            refine ⟨72130364090606859841718075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48086909393737906561145383 72130364090606859841718075)
            ·
              refine ⟨108195546135910289762577113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72130364090606859841718075 108195546135910289762577113)
              ·
                refine ⟨81146659601932717321932835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108195546135910289762577113 81146659601932717321932835)
                ·
                  refine ⟨121719989402899075982899253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81146659601932717321932835 121719989402899075982899253)
                  ·
                    refine ⟨11411249006521788373396805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121719989402899075982899253 11411249006521788373396805)
                    ·
                      refine ⟨2139609188722835320011901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11411249006521788373396805 2139609188722835320011901)
                      ·
                        rfl

theorem cell23_4166874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_4166874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166874 prefixEnd_4166874 := by exact prefixLift 4166874
  have htrace : WordTrace (prefixWord ++ tailWord_4166874) baseStart_4166874 baseEnd_4166874 := by
    simpa [prefixWord, tailWord_4166874, baseEnd_4166874] using wordTrace_append hprefix tailTrace_4166874
  have hstable : (prefixWord ++ tailWord_4166874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166874).length < 2 ^ (prefixWord ++ tailWord_4166874).sum := by decide
  have hdescent : baseEnd_4166874 < baseStart_4166874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166884 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_4166884 : Nat := 118140960795 + 4166884 * 2 ^ 59
def prefixEnd_4166884 : Nat := 4983230072969 + 3 ^ 40 * 4166884 * 2
def baseEnd_4166884 : Nat := 713204774509793426962285

theorem tailTrace_4166884 : CollatzResearch.WordTrace tailWord_4166884 prefixEnd_4166884 713204774509793426962285 := by
  unfold tailWord_4166884
  simp only [CollatzResearch.WordTrace]
  refine ⟨75989372518049194987593853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101319163357398926650125137 75989372518049194987593853)
  ·
    refine ⟨28496014694268448120347695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75989372518049194987593853 28496014694268448120347695)
    ·
      refine ⟨42744022041402672180521543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28496014694268448120347695 42744022041402672180521543)
      ·
        refine ⟨64116033062104008270782315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42744022041402672180521543 64116033062104008270782315)
        ·
          refine ⟨96174049593156012406173473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64116033062104008270782315 96174049593156012406173473)
          ·
            refine ⟨72130537194867009304630105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96174049593156012406173473 72130537194867009304630105)
            ·
              refine ⟨54097902896150256978472579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72130537194867009304630105 54097902896150256978472579)
              ·
                refine ⟨81146854344225385467708869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54097902896150256978472579 81146854344225385467708869)
                ·
                  refine ⟨15215035189542259775195413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81146854344225385467708869 15215035189542259775195413)
                  ·
                    refine ⟨713204774509793426962285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15215035189542259775195413 713204774509793426962285)
                    ·
                      rfl

theorem cell23_4166884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_4166884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166884 prefixEnd_4166884 := by exact prefixLift 4166884
  have htrace : WordTrace (prefixWord ++ tailWord_4166884) baseStart_4166884 baseEnd_4166884 := by
    simpa [prefixWord, tailWord_4166884, baseEnd_4166884] using wordTrace_append hprefix tailTrace_4166884
  have hstable : (prefixWord ++ tailWord_4166884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166884).length < 2 ^ (prefixWord ++ tailWord_4166884).sum := by decide
  have hdescent : baseEnd_4166884 < baseStart_4166884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4166948 : List Nat := [2, 3, 1, 3, 1, 1, 3, 4, 5]
def baseStart_4166948 : Nat := 118140960795 + 4166948 * 2 ^ 59
def prefixEnd_4166948 : Nat := 4983230072969 + 3 ^ 40 * 4166948 * 2
def baseEnd_4166948 : Nat := 237738576254585336720729

theorem tailTrace_4166948 : CollatzResearch.WordTrace tailWord_4166948 prefixEnd_4166948 237738576254585336720729 := by
  unfold tailWord_4166948
  simp only [CollatzResearch.WordTrace]
  refine ⟨75990539653933264452758749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101320719538577685937011665 75990539653933264452758749)
  ·
    refine ⟨28496452370224974169784531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75990539653933264452758749 28496452370224974169784531)
    ·
      refine ⟨42744678555337461254676797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28496452370224974169784531 42744678555337461254676797)
      ·
        refine ⟨16029254458251547970503799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42744678555337461254676797 16029254458251547970503799)
        ·
          refine ⟨24043881687377321955755699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16029254458251547970503799 24043881687377321955755699)
          ·
            refine ⟨36065822531065982933633549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24043881687377321955755699 36065822531065982933633549)
            ·
              refine ⟨13524683449149743600112581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36065822531065982933633549 13524683449149743600112581)
              ·
                refine ⟨2535878146715576925021109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13524683449149743600112581 2535878146715576925021109)
                ·
                  refine ⟨237738576254585336720729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2535878146715576925021109 237738576254585336720729)
                  ·
                    rfl

theorem cell23_4166948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_4166948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4166948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4166948 prefixEnd_4166948 := by exact prefixLift 4166948
  have htrace : WordTrace (prefixWord ++ tailWord_4166948) baseStart_4166948 baseEnd_4166948 := by
    simpa [prefixWord, tailWord_4166948, baseEnd_4166948] using wordTrace_append hprefix tailTrace_4166948
  have hstable : (prefixWord ++ tailWord_4166948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4166948).length < 2 ^ (prefixWord ++ tailWord_4166948).sum := by decide
  have hdescent : baseEnd_4166948 < baseStart_4166948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4166948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167008 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 3, 4]
def baseStart_4167008 : Nat := 118140960795 + 4167008 * 2 ^ 59
def prefixEnd_4167008 : Nat := 4983230072969 + 3 ^ 40 * 4167008 * 2
def baseEnd_4167008 : Nat := 713225998376845931912095

theorem tailTrace_4167008 : CollatzResearch.WordTrace tailWord_4167008 prefixEnd_4167008 713225998376845931912095 := by
  unfold tailWord_4167008
  simp only [CollatzResearch.WordTrace]
  refine ⟨75991633843824579576350839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101322178458432772768467785 75991633843824579576350839)
  ·
    refine ⟨113987450765736869364526259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75991633843824579576350839 113987450765736869364526259)
    ·
      refine ⟨170981176148605304046789389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113987450765736869364526259 170981176148605304046789389)
      ·
        refine ⟨64117941055726989017546021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170981176148605304046789389 64117941055726989017546021)
        ·
          refine ⟨12022113947948810440789879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64117941055726989017546021 12022113947948810440789879)
          ·
            refine ⟨18033170921923215661184819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12022113947948810440789879 18033170921923215661184819)
            ·
              refine ⟨27049756382884823491777229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18033170921923215661184819 27049756382884823491777229)
              ·
                refine ⟨10143658643581808809416461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27049756382884823491777229 10143658643581808809416461)
                ·
                  refine ⟨3803871991343178303531173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10143658643581808809416461 3803871991343178303531173)
                  ·
                    refine ⟨713225998376845931912095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3803871991343178303531173 713225998376845931912095)
                    ·
                      rfl

theorem cell23_4167008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 4].length) (baseStart_4167008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167008 prefixEnd_4167008 := by exact prefixLift 4167008
  have htrace : WordTrace (prefixWord ++ tailWord_4167008) baseStart_4167008 baseEnd_4167008 := by
    simpa [prefixWord, tailWord_4167008, baseEnd_4167008] using wordTrace_append hprefix tailTrace_4167008
  have hstable : (prefixWord ++ tailWord_4167008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167008).length < 2 ^ (prefixWord ++ tailWord_4167008).sum := by decide
  have hdescent : baseEnd_4167008 < baseStart_4167008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167031 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_4167031 : Nat := 118140960795 + 4167031 * 2 ^ 59
def prefixEnd_4167031 : Nat := 4983230072969 + 3 ^ 40 * 4167031 * 2
def baseEnd_4167031 : Nat := 2139689805185591205748679

theorem tailTrace_4167031 : CollatzResearch.WordTrace tailWord_4167031 prefixEnd_4167031 2139689805185591205748679 := by
  unfold tailWord_4167031
  simp only [CollatzResearch.WordTrace]
  refine ⟨151984106566565834080788947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101322737711043889387192631 151984106566565834080788947)
  ·
    refine ⟨227976159849848751121183421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151984106566565834080788947 227976159849848751121183421)
    ·
      refine ⟨85491059943693281670443783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227976159849848751121183421 85491059943693281670443783)
      ·
        refine ⟨128236589915539922505665675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85491059943693281670443783 128236589915539922505665675)
        ·
          refine ⟨192354884873309883758498513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128236589915539922505665675 192354884873309883758498513)
          ·
            refine ⟨144266163654982412818873885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192354884873309883758498513 144266163654982412818873885)
            ·
              refine ⟨54099811370618404807077707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144266163654982412818873885 54099811370618404807077707)
              ·
                refine ⟨81149717055927607210616561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54099811370618404807077707 81149717055927607210616561)
                ·
                  refine ⟨60862287791945705407962421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81149717055927607210616561 60862287791945705407962421)
                  ·
                    refine ⟨5705839480494909881996477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60862287791945705407962421 5705839480494909881996477)
                    ·
                      refine ⟨2139689805185591205748679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5705839480494909881996477 2139689805185591205748679)
                      ·
                        rfl

theorem cell23_4167031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_4167031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167031 prefixEnd_4167031 := by exact prefixLift 4167031
  have htrace : WordTrace (prefixWord ++ tailWord_4167031) baseStart_4167031 baseEnd_4167031 := by
    simpa [prefixWord, tailWord_4167031, baseEnd_4167031] using wordTrace_append hprefix tailTrace_4167031
  have hstable : (prefixWord ++ tailWord_4167031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167031).length < 2 ^ (prefixWord ++ tailWord_4167031).sum := by decide
  have hdescent : baseEnd_4167031 < baseStart_4167031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167065 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 3]
def baseStart_4167065 : Nat := 118140960795 + 4167065 * 2 ^ 59
def prefixEnd_4167065 : Nat := 4983230072969 + 3 ^ 40 * 4167065 * 2
def baseEnd_4167065 : Nat := 2139707263527844072723523

theorem tailTrace_4167065 : CollatzResearch.WordTrace tailWord_4167065 prefixEnd_4167065 2139707263527844072723523 := by
  unfold tailWord_4167065
  simp only [CollatzResearch.WordTrace]
  refine ⟨151985346648442657887526649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101323564432295105258351099 151985346648442657887526649)
  ·
    refine ⟨113989009986331993415644987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151985346648442657887526649 113989009986331993415644987)
    ·
      refine ⟨170983514979497990123467481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113989009986331993415644987 170983514979497990123467481)
      ·
        refine ⟨128237636234623492592600611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170983514979497990123467481 128237636234623492592600611)
        ·
          refine ⟨192356454351935238888900917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128237636234623492592600611 192356454351935238888900917)
          ·
            refine ⟨18033417595493928645834461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192356454351935238888900917 18033417595493928645834461)
            ·
              refine ⟨6762531598310223242187923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18033417595493928645834461 6762531598310223242187923)
              ·
                refine ⟨10143797397465334863281885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762531598310223242187923 10143797397465334863281885)
                ·
                  refine ⟨3803924024049500573730707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10143797397465334863281885 3803924024049500573730707)
                  ·
                    refine ⟨5705886036074250860596061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3803924024049500573730707 5705886036074250860596061)
                    ·
                      refine ⟨2139707263527844072723523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5705886036074250860596061 2139707263527844072723523)
                      ·
                        rfl

theorem cell23_4167065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_4167065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167065 prefixEnd_4167065 := by exact prefixLift 4167065
  have htrace : WordTrace (prefixWord ++ tailWord_4167065) baseStart_4167065 baseEnd_4167065 := by
    simpa [prefixWord, tailWord_4167065, baseEnd_4167065] using wordTrace_append hprefix tailTrace_4167065
  have hstable : (prefixWord ++ tailWord_4167065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167065).length < 2 ^ (prefixWord ++ tailWord_4167065).sum := by decide
  have hdescent : baseEnd_4167065 < baseStart_4167065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167085 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4167085 : Nat := 118140960795 + 4167085 * 2 ^ 59
def prefixEnd_4167085 : Nat := 4983230072969 + 3 ^ 40 * 4167085 * 2
def baseEnd_4167085 : Nat := 713239177713644664824477

theorem tailTrace_4167085 : CollatzResearch.WordTrace tailWord_4167085 prefixEnd_4167085 713239177713644664824477 := by
  unfold tailWord_4167085
  simp only [CollatzResearch.WordTrace]
  refine ⟨151986076108370201303254709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101324050738913467535503139 151986076108370201303254709)
  ·
    refine ⟨14248694635159706372180129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151986076108370201303254709 14248694635159706372180129)
    ·
      refine ⟨10686520976369779779135097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14248694635159706372180129 10686520976369779779135097)
      ·
        refine ⟨8014890732277334834351323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10686520976369779779135097 8014890732277334834351323)
        ·
          refine ⟨12022336098416002251526985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8014890732277334834351323 12022336098416002251526985)
          ·
            refine ⟨9016752073812001688645239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12022336098416002251526985 9016752073812001688645239)
            ·
              refine ⟨13525128110718002532967859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9016752073812001688645239 13525128110718002532967859)
              ·
                refine ⟨20287692166077003799451789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13525128110718002532967859 20287692166077003799451789)
                ·
                  refine ⟨7607884562278876424794421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20287692166077003799451789 7607884562278876424794421)
                  ·
                    refine ⟨713239177713644664824477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7607884562278876424794421 713239177713644664824477)
                    ·
                      rfl

theorem cell23_4167085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4167085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167085 prefixEnd_4167085 := by exact prefixLift 4167085
  have htrace : WordTrace (prefixWord ++ tailWord_4167085) baseStart_4167085 baseEnd_4167085 := by
    simpa [prefixWord, tailWord_4167085, baseEnd_4167085] using wordTrace_append hprefix tailTrace_4167085
  have hstable : (prefixWord ++ tailWord_4167085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167085).length < 2 ^ (prefixWord ++ tailWord_4167085).sum := by decide
  have hdescent : baseEnd_4167085 < baseStart_4167085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167088 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 4]
def baseStart_4167088 : Nat := 118140960795 + 4167088 * 2 ^ 59
def prefixEnd_4167088 : Nat := 4983230072969 + 3 ^ 40 * 4167088 * 2
def baseEnd_4167088 : Nat := 2139719073582897482735917

theorem tailTrace_4167088 : CollatzResearch.WordTrace tailWord_4167088 prefixEnd_4167088 2139719073582897482735917 := by
  unfold tailWord_4167088
  simp only [CollatzResearch.WordTrace]
  refine ⟨75993092763679666407806959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101324123684906221877075945 75993092763679666407806959)
  ·
    refine ⟨113989639145519499611710439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75993092763679666407806959 113989639145519499611710439)
    ·
      refine ⟨170984458718279249417565659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113989639145519499611710439 170984458718279249417565659)
      ·
        refine ⟨256476688077418874126348489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170984458718279249417565659 256476688077418874126348489)
        ·
          refine ⟨192357516058064155594761367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256476688077418874126348489 192357516058064155594761367)
          ·
            refine ⟨288536274087096233392142051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192357516058064155594761367 288536274087096233392142051)
            ·
              refine ⟨432804411130644350088213077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288536274087096233392142051 432804411130644350088213077)
              ·
                refine ⟨5071926692937238477596247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 432804411130644350088213077 5071926692937238477596247)
                ·
                  refine ⟨7607890039405857716394371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071926692937238477596247 7607890039405857716394371)
                  ·
                    refine ⟨11411835059108786574591557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7607890039405857716394371 11411835059108786574591557)
                    ·
                      refine ⟨2139719073582897482735917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11411835059108786574591557 2139719073582897482735917)
                      ·
                        rfl

theorem cell23_4167088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 4].length) (baseStart_4167088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167088 prefixEnd_4167088 := by exact prefixLift 4167088
  have htrace : WordTrace (prefixWord ++ tailWord_4167088) baseStart_4167088 baseEnd_4167088 := by
    simpa [prefixWord, tailWord_4167088, baseEnd_4167088] using wordTrace_append hprefix tailTrace_4167088
  have hstable : (prefixWord ++ tailWord_4167088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167088).length < 2 ^ (prefixWord ++ tailWord_4167088).sum := by decide
  have hdescent : baseEnd_4167088 < baseStart_4167088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167091 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 5]
def baseStart_4167091 : Nat := 118140960795 + 4167091 * 2 ^ 59
def prefixEnd_4167091 : Nat := 4983230072969 + 3 ^ 40 * 4167091 * 2
def baseEnd_4167091 : Nat := 2139720614024860970998403

theorem tailTrace_4167091 : CollatzResearch.WordTrace tailWord_4167091 prefixEnd_4167091 2139720614024860970998403 := by
  unfold tailWord_4167091
  simp only [CollatzResearch.WordTrace]
  refine ⟨151986294946348464327973127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101324196630898976218648751 151986294946348464327973127)
  ·
    refine ⟨227979442419522696491959691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151986294946348464327973127 227979442419522696491959691)
    ·
      refine ⟨341969163629284044737939537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227979442419522696491959691 341969163629284044737939537)
      ·
        refine ⟨256476872721963033553454653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341969163629284044737939537 256476872721963033553454653)
        ·
          refine ⟨96178827270736137582545495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256476872721963033553454653 96178827270736137582545495)
          ·
            refine ⟨144268240906104206373818243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96178827270736137582545495 144268240906104206373818243)
            ·
              refine ⟨216402361359156309560727365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144268240906104206373818243 216402361359156309560727365)
              ·
                refine ⟨40575442754841808042636381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216402361359156309560727365 40575442754841808042636381)
                ·
                  refine ⟨15215791033065678015988643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40575442754841808042636381 15215791033065678015988643)
                  ·
                    refine ⟨22823686549598517023982965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15215791033065678015988643 22823686549598517023982965)
                    ·
                      refine ⟨2139720614024860970998403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22823686549598517023982965 2139720614024860970998403)
                      ·
                        rfl

theorem cell23_4167091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_4167091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167091 prefixEnd_4167091 := by exact prefixLift 4167091
  have htrace : WordTrace (prefixWord ++ tailWord_4167091) baseStart_4167091 baseEnd_4167091 := by
    simpa [prefixWord, tailWord_4167091, baseEnd_4167091] using wordTrace_append hprefix tailTrace_4167091
  have hstable : (prefixWord ++ tailWord_4167091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167091).length < 2 ^ (prefixWord ++ tailWord_4167091).sum := by decide
  have hdescent : baseEnd_4167091 < baseStart_4167091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167106 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4167106 : Nat := 118140960795 + 4167106 * 2 ^ 59
def prefixEnd_4167106 : Nat := 4983230072969 + 3 ^ 40 * 4167106 * 2
def baseEnd_4167106 : Nat := 237747590692742045812315

theorem tailTrace_4167106 : CollatzResearch.WordTrace tailWord_4167106 prefixEnd_4167106 237747590692742045812315 := by
  unfold tailWord_4167106
  simp only [CollatzResearch.WordTrace]
  refine ⟨37996710510323530472442293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101324561360862747926512781 37996710510323530472442293)
  ·
    refine ⟨3562191610342830981791465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37996710510323530472442293 3562191610342830981791465)
    ·
      refine ⟨2671643707757123236343599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3562191610342830981791465 2671643707757123236343599)
      ·
        refine ⟨4007465561635684854515399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671643707757123236343599 4007465561635684854515399)
        ·
          refine ⟨6011198342453527281773099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007465561635684854515399 6011198342453527281773099)
          ·
            refine ⟨9016797513680290922659649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6011198342453527281773099 9016797513680290922659649)
            ·
              refine ⟨6762598135260218191994737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9016797513680290922659649 6762598135260218191994737)
              ·
                refine ⟨5071948601445163643996053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762598135260218191994737 5071948601445163643996053)
                ·
                  refine ⟨237747590692742045812315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5071948601445163643996053 237747590692742045812315)
                  ·
                    rfl

theorem cell23_4167106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4167106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167106 prefixEnd_4167106 := by exact prefixLift 4167106
  have htrace : WordTrace (prefixWord ++ tailWord_4167106) baseStart_4167106 baseEnd_4167106 := by
    simpa [prefixWord, tailWord_4167106, baseEnd_4167106] using wordTrace_append hprefix tailTrace_4167106
  have hstable : (prefixWord ++ tailWord_4167106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167106).length < 2 ^ (prefixWord ++ tailWord_4167106).sum := by decide
  have hdescent : baseEnd_4167106 < baseStart_4167106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167116 : List Nat := [2, 2, 1, 4, 2, 3, 2, 2, 1, 1, 3]
def baseStart_4167116 : Nat := 118140960795 + 4167116 * 2 ^ 59
def prefixEnd_4167116 : Nat := 4983230072969 + 3 ^ 40 * 4167116 * 2
def baseEnd_4167116 : Nat := 2139733451041223373185789

theorem tailTrace_4167116 : CollatzResearch.WordTrace tailWord_4167116 prefixEnd_4167116 2139733451041223373185789 := by
  unfold tailWord_4167116
  simp only [CollatzResearch.WordTrace]
  refine ⟨75993603385628946798816601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101324804514171929065088801 75993603385628946798816601)
  ·
    refine ⟨56995202539221710099112451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75993603385628946798816601 56995202539221710099112451)
    ·
      refine ⟨85492803808832565148668677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56995202539221710099112451 85492803808832565148668677)
      ·
        refine ⟨16029900714156105965375377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85492803808832565148668677 16029900714156105965375377)
        ·
          refine ⟨12022425535617079474031533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16029900714156105965375377 12022425535617079474031533)
          ·
            refine ⟨4508409575856404802761825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12022425535617079474031533 4508409575856404802761825)
            ·
              refine ⟨3381307181892303602071369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508409575856404802761825 3381307181892303602071369)
              ·
                refine ⟨2535980386419227701553527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381307181892303602071369 2535980386419227701553527)
                ·
                  refine ⟨3803970579628841552330291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2535980386419227701553527 3803970579628841552330291)
                  ·
                    refine ⟨5705955869443262328495437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3803970579628841552330291 5705955869443262328495437)
                    ·
                      refine ⟨2139733451041223373185789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5705955869443262328495437 2139733451041223373185789)
                      ·
                        rfl

theorem cell23_4167116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_4167116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167116 prefixEnd_4167116 := by exact prefixLift 4167116
  have htrace : WordTrace (prefixWord ++ tailWord_4167116) baseStart_4167116 baseEnd_4167116 := by
    simpa [prefixWord, tailWord_4167116, baseEnd_4167116] using wordTrace_append hprefix tailTrace_4167116
  have hstable : (prefixWord ++ tailWord_4167116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167116).length < 2 ^ (prefixWord ++ tailWord_4167116).sum := by decide
  have hdescent : baseEnd_4167116 < baseStart_4167116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167166 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_4167166 : Nat := 118140960795 + 4167166 * 2 ^ 59
def prefixEnd_4167166 : Nat := 4983230072969 + 3 ^ 40 * 4167166 * 2
def baseEnd_4167166 : Nat := 713253041691316059186853

theorem tailTrace_4167166 : CollatzResearch.WordTrace tailWord_4167166 prefixEnd_4167166 713253041691316059186853 := by
  unfold tailWord_4167166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18998628802634594017119169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101326020280717834757968901 18998628802634594017119169)
  ·
    refine ⟨14248971601975945512839377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18998628802634594017119169 14248971601975945512839377)
    ·
      refine ⟨10686728701481959134629533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14248971601975945512839377 10686728701481959134629533)
      ·
        refine ⟨4007523263055734675486075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10686728701481959134629533 4007523263055734675486075)
        ·
          refine ⟨6011284894583602013229113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007523263055734675486075 6011284894583602013229113)
          ·
            refine ⟨4508463670937701509921835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6011284894583602013229113 4508463670937701509921835)
            ·
              refine ⟨6762695506406552264882753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508463670937701509921835 6762695506406552264882753)
              ·
                refine ⟨5072021629804914198662065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762695506406552264882753 5072021629804914198662065)
                ·
                  refine ⟨3804016222353685648996549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5072021629804914198662065 3804016222353685648996549)
                  ·
                    refine ⟨713253041691316059186853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3804016222353685648996549 713253041691316059186853)
                    ·
                      rfl

theorem cell23_4167166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_4167166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167166 prefixEnd_4167166 := by exact prefixLift 4167166
  have htrace : WordTrace (prefixWord ++ tailWord_4167166) baseStart_4167166 baseEnd_4167166 := by
    simpa [prefixWord, tailWord_4167166, baseEnd_4167166] using wordTrace_append hprefix tailTrace_4167166
  have hstable : (prefixWord ++ tailWord_4167166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167166).length < 2 ^ (prefixWord ++ tailWord_4167166).sum := by decide
  have hdescent : baseEnd_4167166 < baseStart_4167166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167189 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_4167189 : Nat := 118140960795 + 4167189 * 2 ^ 59
def prefixEnd_4167189 : Nat := 4983230072969 + 3 ^ 40 * 4167189 * 2
def baseEnd_4167189 : Nat := 2139770935129001587572953

theorem tailTrace_4167189 : CollatzResearch.WordTrace tailWord_4167189 prefixEnd_4167189 2139770935129001587572953 := by
  unfold tailWord_4167189
  simp only [CollatzResearch.WordTrace]
  refine ⟨151989869299993427065040621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101326579533328951376693747 151989869299993427065040621)
  ·
    refine ⟨56996200987497535149390233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151989869299993427065040621 56996200987497535149390233)
    ·
      refine ⟨42747150740623151362042675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56996200987497535149390233 42747150740623151362042675)
      ·
        refine ⟨64120726110934727043064013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42747150740623151362042675 64120726110934727043064013)
        ·
          refine ⟨24045272291600522641149005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64120726110934727043064013 24045272291600522641149005)
          ·
            refine ⟨9016977109350195990430877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24045272291600522641149005 9016977109350195990430877)
            ·
              refine ⟨3381366416006323496411579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9016977109350195990430877 3381366416006323496411579)
              ·
                refine ⟨5072049624009485244617369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3381366416006323496411579 5072049624009485244617369)
                ·
                  refine ⟨3804037218007113933463027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5072049624009485244617369 3804037218007113933463027)
                  ·
                    refine ⟨5706055827010670900194541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3804037218007113933463027 5706055827010670900194541)
                    ·
                      refine ⟨2139770935129001587572953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5706055827010670900194541 2139770935129001587572953)
                      ·
                        rfl

theorem cell23_4167189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_4167189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167189 prefixEnd_4167189 := by exact prefixLift 4167189
  have htrace : WordTrace (prefixWord ++ tailWord_4167189) baseStart_4167189 baseEnd_4167189 := by
    simpa [prefixWord, tailWord_4167189, baseEnd_4167189] using wordTrace_append hprefix tailTrace_4167189
  have hstable : (prefixWord ++ tailWord_4167189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167189).length < 2 ^ (prefixWord ++ tailWord_4167189).sum := by decide
  have hdescent : baseEnd_4167189 < baseStart_4167189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167248 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 4, 5]
def baseStart_4167248 : Nat := 118140960795 + 4167248 * 2 ^ 59
def prefixEnd_4167248 : Nat := 4983230072969 + 3 ^ 40 * 4167248 * 2
def baseEnd_4167248 : Nat := 713267076829205618911727

theorem tailTrace_4167248 : CollatzResearch.WordTrace tailWord_4167248 prefixEnd_4167248 713267076829205618911727 := by
  unfold tailWord_4167248
  simp only [CollatzResearch.WordTrace]
  refine ⟨75996010603389840070719199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101328014137853120094292265 75996010603389840070719199)
  ·
    refine ⟨113994015905084760106078799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75996010603389840070719199 113994015905084760106078799)
    ·
      refine ⟨170991023857627140159118199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113994015905084760106078799 170991023857627140159118199)
      ·
        refine ⟨256486535786440710238677299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170991023857627140159118199 256486535786440710238677299)
        ·
          refine ⟨384729803679661065358015949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256486535786440710238677299 384729803679661065358015949)
          ·
            refine ⟨144273676379872899509255981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384729803679661065358015949 144273676379872899509255981)
            ·
              refine ⟨54102628642452337315970993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144273676379872899509255981 54102628642452337315970993)
              ·
                refine ⟨40576971481839252986978245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54102628642452337315970993 40576971481839252986978245)
                ·
                  refine ⟨7608182152844859935058421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40576971481839252986978245 7608182152844859935058421)
                  ·
                    refine ⟨713267076829205618911727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7608182152844859935058421 713267076829205618911727)
                    ·
                      rfl

theorem cell23_4167248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_4167248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167248 prefixEnd_4167248 := by exact prefixLift 4167248
  have htrace : WordTrace (prefixWord ++ tailWord_4167248) baseStart_4167248 baseEnd_4167248 := by
    simpa [prefixWord, tailWord_4167248, baseEnd_4167248] using wordTrace_append hprefix tailTrace_4167248
  have hstable : (prefixWord ++ tailWord_4167248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167248).length < 2 ^ (prefixWord ++ tailWord_4167248).sum := by decide
  have hdescent : baseEnd_4167248 < baseStart_4167248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167265 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 2, 5]
def baseStart_4167265 : Nat := 118140960795 + 4167265 * 2 ^ 59
def prefixEnd_4167265 : Nat := 4983230072969 + 3 ^ 40 * 4167265 * 2
def baseEnd_4167265 : Nat := 713269986552914430074201

theorem tailTrace_4167265 : CollatzResearch.WordTrace tailWord_4167265 prefixEnd_4167265 713269986552914430074201 := by
  unfold tailWord_4167265
  simp only [CollatzResearch.WordTrace]
  refine ⟨151992641247718092044807249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101328427498478728029871499 151992641247718092044807249)
  ·
    refine ⟨113994480935788569033605437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151992641247718092044807249 113994480935788569033605437)
    ·
      refine ⟨42747930350920713387602039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113994480935788569033605437 42747930350920713387602039)
      ·
        refine ⟨64121895526381070081403059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42747930350920713387602039 64121895526381070081403059)
        ·
          refine ⟨96182843289571605122104589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64121895526381070081403059 96182843289571605122104589)
          ·
            refine ⟨36068566233589351920789221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96182843289571605122104589 36068566233589351920789221)
            ·
              refine ⟨6762856168798003485147979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36068566233589351920789221 6762856168798003485147979)
              ·
                refine ⟨10144284253197005227721969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762856168798003485147979 10144284253197005227721969)
                ·
                  refine ⟨7608213189897753920791477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10144284253197005227721969 7608213189897753920791477)
                  ·
                    refine ⟨713269986552914430074201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7608213189897753920791477 713269986552914430074201)
                    ·
                      rfl

theorem cell23_4167265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_4167265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167265 prefixEnd_4167265 := by exact prefixLift 4167265
  have htrace : WordTrace (prefixWord ++ tailWord_4167265) baseStart_4167265 baseEnd_4167265 := by
    simpa [prefixWord, tailWord_4167265, baseEnd_4167265] using wordTrace_append hprefix tailTrace_4167265
  have hstable : (prefixWord ++ tailWord_4167265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167265).length < 2 ^ (prefixWord ++ tailWord_4167265).sum := by decide
  have hdescent : baseEnd_4167265 < baseStart_4167265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167286 : List Nat := [5, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_4167286 : Nat := 118140960795 + 4167286 * 2 ^ 59
def prefixEnd_4167286 : Nat := 4983230072969 + 3 ^ 40 * 4167286 * 2
def baseEnd_4167286 : Nat := 237757860305831967562223

theorem tailTrace_4167286 : CollatzResearch.WordTrace tailWord_4167286 prefixEnd_4167286 237757860305831967562223 := by
  unfold tailWord_4167286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9499587948790125789457607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101328938120428008420881141 9499587948790125789457607)
  ·
    refine ⟨14249381923185188684186411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9499587948790125789457607 14249381923185188684186411)
    ·
      refine ⟨21374072884777783026279617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14249381923185188684186411 21374072884777783026279617)
      ·
        refine ⟨16030554663583337269709713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21374072884777783026279617 16030554663583337269709713)
        ·
          refine ⟨12022915997687502952282285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16030554663583337269709713 12022915997687502952282285)
          ·
            refine ⟨4508593499132813607105857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12022915997687502952282285 4508593499132813607105857)
            ·
              refine ⟨3381445124349610205329393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508593499132813607105857 3381445124349610205329393)
              ·
                refine ⟨2536083843262207653997045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381445124349610205329393 2536083843262207653997045)
                ·
                  refine ⟨237757860305831967562223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2536083843262207653997045 237757860305831967562223)
                  ·
                    rfl

theorem cell23_4167286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_4167286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167286 prefixEnd_4167286 := by exact prefixLift 4167286
  have htrace : WordTrace (prefixWord ++ tailWord_4167286) baseStart_4167286 baseEnd_4167286 := by
    simpa [prefixWord, tailWord_4167286, baseEnd_4167286] using wordTrace_append hprefix tailTrace_4167286
  have hstable : (prefixWord ++ tailWord_4167286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167286).length < 2 ^ (prefixWord ++ tailWord_4167286).sum := by decide
  have hdescent : baseEnd_4167286 < baseStart_4167286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167305 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 3]
def baseStart_4167305 : Nat := 118140960795 + 4167305 * 2 ^ 59
def prefixEnd_4167305 : Nat := 4983230072969 + 3 ^ 40 * 4167305 * 2
def baseEnd_4167305 : Nat := 2139830498884923133722419

theorem tailTrace_4167305 : CollatzResearch.WordTrace tailWord_4167305 prefixEnd_4167305 2139830498884923133722419 := by
  unfold tailWord_4167305
  simp only [CollatzResearch.WordTrace]
  refine ⟨151994100167573178876263369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101329400111715452584175579 151994100167573178876263369)
  ·
    refine ⟨113995575125679884157197527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151994100167573178876263369 113995575125679884157197527)
    ·
      refine ⟨170993362688519826235796291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113995575125679884157197527 170993362688519826235796291)
      ·
        refine ⟨256490044032779739353694437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170993362688519826235796291 256490044032779739353694437)
        ·
          refine ⟨48091883256146201128817707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256490044032779739353694437 48091883256146201128817707)
          ·
            refine ⟨72137824884219301693226561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48091883256146201128817707 72137824884219301693226561)
            ·
              refine ⟨54103368663164476269919921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72137824884219301693226561 54103368663164476269919921)
              ·
                refine ⟨40577526497373357202439941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54103368663164476269919921 40577526497373357202439941)
                ·
                  refine ⟨7608286218257504475457489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40577526497373357202439941 7608286218257504475457489)
                  ·
                    refine ⟨5706214663693128356593117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7608286218257504475457489 5706214663693128356593117)
                    ·
                      refine ⟨2139830498884923133722419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5706214663693128356593117 2139830498884923133722419)
                      ·
                        rfl

theorem cell23_4167305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 2, 3].length) (baseStart_4167305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167305 prefixEnd_4167305 := by exact prefixLift 4167305
  have htrace : WordTrace (prefixWord ++ tailWord_4167305) baseStart_4167305 baseEnd_4167305 := by
    simpa [prefixWord, tailWord_4167305, baseEnd_4167305] using wordTrace_append hprefix tailTrace_4167305
  have hstable : (prefixWord ++ tailWord_4167305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167305).length < 2 ^ (prefixWord ++ tailWord_4167305).sum := by decide
  have hdescent : baseEnd_4167305 < baseStart_4167305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167316 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_4167316 : Nat := 118140960795 + 4167316 * 2 ^ 59
def prefixEnd_4167316 : Nat := 4983230072969 + 3 ^ 40 * 4167316 * 2
def baseEnd_4167316 : Nat := 713278715724040863561623

theorem tailTrace_4167316 : CollatzResearch.WordTrace tailWord_4167316 prefixEnd_4167316 713278715724040863561623 := by
  unfold tailWord_4167316
  simp only [CollatzResearch.WordTrace]
  refine ⟨75997250685266663877456901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101329667580355551836609201 75997250685266663877456901)
  ·
    refine ⟨14249484503487499477023169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75997250685266663877456901 14249484503487499477023169)
    ·
      refine ⟨10687113377615624607767377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14249484503487499477023169 10687113377615624607767377)
      ·
        refine ⟨8015335033211718455825533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10687113377615624607767377 8015335033211718455825533)
        ·
          refine ⟨3005750637454394420934575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8015335033211718455825533 3005750637454394420934575)
          ·
            refine ⟨4508625956181591631401863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3005750637454394420934575 4508625956181591631401863)
            ·
              refine ⟨6762938934272387447102795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4508625956181591631401863 6762938934272387447102795)
              ·
                refine ⟨10144408401408581170654193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762938934272387447102795 10144408401408581170654193)
                ·
                  refine ⟨7608306301056435877990645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10144408401408581170654193 7608306301056435877990645)
                  ·
                    refine ⟨713278715724040863561623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7608306301056435877990645 713278715724040863561623)
                    ·
                      rfl

theorem cell23_4167316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_4167316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167316 prefixEnd_4167316 := by exact prefixLift 4167316
  have htrace : WordTrace (prefixWord ++ tailWord_4167316) baseStart_4167316 baseEnd_4167316 := by
    simpa [prefixWord, tailWord_4167316, baseEnd_4167316] using wordTrace_append hprefix tailTrace_4167316
  have hstable : (prefixWord ++ tailWord_4167316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167316).length < 2 ^ (prefixWord ++ tailWord_4167316).sum := by decide
  have hdescent : baseEnd_4167316 < baseStart_4167316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167329 : List Nat := [1, 2, 3, 3, 2, 1, 1, 5, 1, 4]
def baseStart_4167329 : Nat := 118140960795 + 4167329 * 2 ^ 59
def prefixEnd_4167329 : Nat := 4983230072969 + 3 ^ 40 * 4167329 * 2
def baseEnd_4167329 : Nat := 713280940806877013274103

theorem tailTrace_4167329 : CollatzResearch.WordTrace tailWord_4167329 prefixEnd_4167329 713280940806877013274103 := by
  unfold tailWord_4167329
  simp only [CollatzResearch.WordTrace]
  refine ⟨151994975519486230975137041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101329983679657487316758027 151994975519486230975137041)
  ·
    refine ⟨113996231639614673231352781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151994975519486230975137041 113996231639614673231352781)
    ·
      refine ⟨42748586864855502461757293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113996231639614673231352781 42748586864855502461757293)
      ·
        refine ⟨16030720074320813423158985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42748586864855502461757293 16030720074320813423158985)
        ·
          refine ⟨12023040055740610067369239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16030720074320813423158985 12023040055740610067369239)
          ·
            refine ⟨18034560083610915101053859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12023040055740610067369239 18034560083610915101053859)
            ·
              refine ⟨27051840125416372651580789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18034560083610915101053859 27051840125416372651580789)
              ·
                refine ⟨2536110011757784936085699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27051840125416372651580789 2536110011757784936085699)
                ·
                  refine ⟨3804165017636677404128549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536110011757784936085699 3804165017636677404128549)
                  ·
                    refine ⟨713280940806877013274103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3804165017636677404128549 713280940806877013274103)
                    ·
                      rfl

theorem cell23_4167329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_4167329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167329 prefixEnd_4167329 := by exact prefixLift 4167329
  have htrace : WordTrace (prefixWord ++ tailWord_4167329) baseStart_4167329 baseEnd_4167329 := by
    simpa [prefixWord, tailWord_4167329, baseEnd_4167329] using wordTrace_append hprefix tailTrace_4167329
  have hstable : (prefixWord ++ tailWord_4167329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167329).length < 2 ^ (prefixWord ++ tailWord_4167329).sum := by decide
  have hdescent : baseEnd_4167329 < baseStart_4167329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167375 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_4167375 : Nat := 118140960795 + 4167375 * 2 ^ 59
def prefixEnd_4167375 : Nat := 4983230072969 + 3 ^ 40 * 4167375 * 2
def baseEnd_4167375 : Nat := 2139866442530737859847097

theorem tailTrace_4167375 : CollatzResearch.WordTrace tailWord_4167375 prefixEnd_4167375 2139866442530737859847097 := by
  unfold tailWord_4167375
  simp only [CollatzResearch.WordTrace]
  refine ⟨151996653277319580831311579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101331102184879720554207719 151996653277319580831311579)
  ·
    refine ⟨227994979915979371246967369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151996653277319580831311579 227994979915979371246967369)
    ·
      refine ⟨170996234936984528435225527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227994979915979371246967369 170996234936984528435225527)
      ·
        refine ⟨256494352405476792652838291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170996234936984528435225527 256494352405476792652838291)
        ·
          refine ⟨384741528608215188979257437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256494352405476792652838291 384741528608215188979257437)
          ·
            refine ⟨144278073228080695867221539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384741528608215188979257437 144278073228080695867221539)
            ·
              refine ⟨216417109842121043800832309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144278073228080695867221539 216417109842121043800832309)
              ·
                refine ⟨20289104047698847856328029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216417109842121043800832309 20289104047698847856328029)
                ·
                  refine ⟨7608414017887067946123011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20289104047698847856328029 7608414017887067946123011)
                  ·
                    refine ⟨11412621026830601919184517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7608414017887067946123011 11412621026830601919184517)
                    ·
                      refine ⟨2139866442530737859847097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11412621026830601919184517 2139866442530737859847097)
                      ·
                        rfl

theorem cell23_4167375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_4167375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167375 prefixEnd_4167375 := by exact prefixLift 4167375
  have htrace : WordTrace (prefixWord ++ tailWord_4167375) baseStart_4167375 baseEnd_4167375 := by
    simpa [prefixWord, tailWord_4167375, baseEnd_4167375] using wordTrace_append hprefix tailTrace_4167375
  have hstable : (prefixWord ++ tailWord_4167375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167375).length < 2 ^ (prefixWord ++ tailWord_4167375).sum := by decide
  have hdescent : baseEnd_4167375 < baseStart_4167375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167386 : List Nat := [3, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3]
def baseStart_4167386 : Nat := 118140960795 + 4167386 * 2 ^ 59
def prefixEnd_4167386 : Nat := 4983230072969 + 3 ^ 40 * 4167386 * 2
def baseEnd_4167386 : Nat := 2139872090817937316809547

theorem tailTrace_4167386 : CollatzResearch.WordTrace tailWord_4167386 prefixEnd_4167386 2139872090817937316809547 := by
  unfold tailWord_4167386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37999263620069932427490503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101331369653519819806641341 37999263620069932427490503)
  ·
    refine ⟨56998895430104898641235755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37999263620069932427490503 56998895430104898641235755)
    ·
      refine ⟨85498343145157347961853633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56998895430104898641235755 85498343145157347961853633)
      ·
        refine ⟨64123757358868010971390225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85498343145157347961853633 64123757358868010971390225)
        ·
          refine ⟨48092818019151008228542669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64123757358868010971390225 48092818019151008228542669)
          ·
            refine ⟨18034806757181628085703501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48092818019151008228542669 18034806757181628085703501)
            ·
              refine ⟨6763052533943110532138813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18034806757181628085703501 6763052533943110532138813)
              ·
                refine ⟨2536144700228666449552055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6763052533943110532138813 2536144700228666449552055)
                ·
                  refine ⟨3804217050342999674328083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536144700228666449552055 3804217050342999674328083)
                  ·
                    refine ⟨5706325575514499511492125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3804217050342999674328083 5706325575514499511492125)
                    ·
                      refine ⟨2139872090817937316809547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5706325575514499511492125 2139872090817937316809547)
                      ·
                        rfl

theorem cell23_4167386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_4167386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167386 prefixEnd_4167386 := by exact prefixLift 4167386
  have htrace : WordTrace (prefixWord ++ tailWord_4167386) baseStart_4167386 baseEnd_4167386 := by
    simpa [prefixWord, tailWord_4167386, baseEnd_4167386] using wordTrace_append hprefix tailTrace_4167386
  have hstable : (prefixWord ++ tailWord_4167386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167386).length < 2 ^ (prefixWord ++ tailWord_4167386).sum := by decide
  have hdescent : baseEnd_4167386 < baseStart_4167386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167392 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 4]
def baseStart_4167392 : Nat := 118140960795 + 4167392 * 2 ^ 59
def prefixEnd_4167392 : Nat := 4983230072969 + 3 ^ 40 * 4167392 * 2
def baseEnd_4167392 : Nat := 2139875171701864293334519

theorem tailTrace_4167392 : CollatzResearch.WordTrace tailWord_4167392 prefixEnd_4167392 2139875171701864293334519 := by
  unfold tailWord_4167392
  simp only [CollatzResearch.WordTrace]
  refine ⟨75998636659128996367340215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101331515545505328489786953 75998636659128996367340215)
  ·
    refine ⟨113997954988693494551010323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75998636659128996367340215 113997954988693494551010323)
    ·
      refine ⟨170996932483040241826515485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113997954988693494551010323 170996932483040241826515485)
      ·
        refine ⟨64123849681140090684943307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170996932483040241826515485 64123849681140090684943307)
        ·
          refine ⟨96185774521710136027414961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64123849681140090684943307 96185774521710136027414961)
          ·
            refine ⟨72139330891282602020561221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96185774521710136027414961 72139330891282602020561221)
            ·
              refine ⟨13526124542115487878855229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72139330891282602020561221 13526124542115487878855229)
              ·
                refine ⟨5072296703293307954570711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13526124542115487878855229 5072296703293307954570711)
                ·
                  refine ⟨7608445054939961931856067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072296703293307954570711 7608445054939961931856067)
                  ·
                    refine ⟨11412667582409942897784101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7608445054939961931856067 11412667582409942897784101)
                    ·
                      refine ⟨2139875171701864293334519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11412667582409942897784101 2139875171701864293334519)
                      ·
                        rfl

theorem cell23_4167392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_4167392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167392 prefixEnd_4167392 := by exact prefixLift 4167392
  have htrace : WordTrace (prefixWord ++ tailWord_4167392) baseStart_4167392 baseEnd_4167392 := by
    simpa [prefixWord, tailWord_4167392, baseEnd_4167392] using wordTrace_append hprefix tailTrace_4167392
  have hstable : (prefixWord ++ tailWord_4167392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167392).length < 2 ^ (prefixWord ++ tailWord_4167392).sum := by decide
  have hdescent : baseEnd_4167392 < baseStart_4167392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167402 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_4167402 : Nat := 118140960795 + 4167402 * 2 ^ 59
def prefixEnd_4167402 : Nat := 4983230072969 + 3 ^ 40 * 4167402 * 2
def baseEnd_4167402 : Nat := 713293435502803084736491

theorem tailTrace_4167402 : CollatzResearch.WordTrace tailWord_4167402 prefixEnd_4167402 713293435502803084736491 := by
  unfold tailWord_4167402
  simp only [CollatzResearch.WordTrace]
  refine ⟨37999409512055441110636115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101331758698814509628362973 37999409512055441110636115)
  ·
    refine ⟨56999114268083161665954173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37999409512055441110636115 56999114268083161665954173)
    ·
      refine ⟨21374667850531185624732815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56999114268083161665954173 21374667850531185624732815)
      ·
        refine ⟨32062001775796778437099223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21374667850531185624732815 32062001775796778437099223)
        ·
          refine ⟨48093002663695167655648835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32062001775796778437099223 48093002663695167655648835)
          ·
            refine ⟨72139503995542751483473253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48093002663695167655648835 72139503995542751483473253)
            ·
              refine ⟨13526156999164265903151235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72139503995542751483473253 13526156999164265903151235)
              ·
                refine ⟨20289235498746398854726853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13526156999164265903151235 20289235498746398854726853)
                ·
                  refine ⟨3804231656014949785261285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20289235498746398854726853 3804231656014949785261285)
                  ·
                    refine ⟨713293435502803084736491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3804231656014949785261285 713293435502803084736491)
                    ·
                      rfl

theorem cell23_4167402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_4167402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167402 prefixEnd_4167402 := by exact prefixLift 4167402
  have htrace : WordTrace (prefixWord ++ tailWord_4167402) baseStart_4167402 baseEnd_4167402 := by
    simpa [prefixWord, tailWord_4167402, baseEnd_4167402] using wordTrace_append hprefix tailTrace_4167402
  have hstable : (prefixWord ++ tailWord_4167402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167402).length < 2 ^ (prefixWord ++ tailWord_4167402).sum := by decide
  have hdescent : baseEnd_4167402 < baseStart_4167402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167426 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_4167426 : Nat := 118140960795 + 4167426 * 2 ^ 59
def prefixEnd_4167426 : Nat := 4983230072969 + 3 ^ 40 * 4167426 * 2
def baseEnd_4167426 : Nat := 2139892630044117160309363

theorem tailTrace_4167426 : CollatzResearch.WordTrace tailWord_4167426 prefixEnd_4167426 2139892630044117160309363 := by
  unfold tailWord_4167426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37999628350033704135354533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101332342266756544360945421 37999628350033704135354533)
  ·
    refine ⟨7124930315631319525378975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37999628350033704135354533 7124930315631319525378975)
    ·
      refine ⟨10687395473446979288068463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7124930315631319525378975 10687395473446979288068463)
      ·
        refine ⟨16031093210170468932102695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10687395473446979288068463 16031093210170468932102695)
        ·
          refine ⟨24046639815255703398154043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16031093210170468932102695 24046639815255703398154043)
          ·
            refine ⟨36069959722883555097231065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24046639815255703398154043 36069959722883555097231065)
            ·
              refine ⟨27052469792162666322923299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36069959722883555097231065 27052469792162666322923299)
              ·
                refine ⟨40578704688243999484384949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27052469792162666322923299 40578704688243999484384949)
                ·
                  refine ⟨3804253564522874951661089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40578704688243999484384949 3804253564522874951661089)
                  ·
                    refine ⟨2853190173392156213745817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3804253564522874951661089 2853190173392156213745817)
                    ·
                      refine ⟨2139892630044117160309363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2853190173392156213745817 2139892630044117160309363)
                      ·
                        rfl

theorem cell23_4167426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_4167426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167426 prefixEnd_4167426 := by exact prefixLift 4167426
  have htrace : WordTrace (prefixWord ++ tailWord_4167426) baseStart_4167426 baseEnd_4167426 := by
    simpa [prefixWord, tailWord_4167426, baseEnd_4167426] using wordTrace_append hprefix tailTrace_4167426
  have hstable : (prefixWord ++ tailWord_4167426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167426).length < 2 ^ (prefixWord ++ tailWord_4167426).sum := by decide
  have hdescent : baseEnd_4167426 < baseStart_4167426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167454 : List Nat := [4, 3, 2, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4167454 : Nat := 118140960795 + 4167454 * 2 ^ 59
def prefixEnd_4167454 : Nat := 4983230072969 + 3 ^ 40 * 4167454 * 2
def baseEnd_4167454 : Nat := 2139907007502443050759235

theorem tailTrace_4167454 : CollatzResearch.WordTrace tailWord_4167454 prefixEnd_4167454 2139907007502443050759235 := by
  unfold tailWord_4167454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18999941830504172165429677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101333023096022251548958277 18999941830504172165429677)
  ·
    refine ⟨7124978186439064562036129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18999941830504172165429677 7124978186439064562036129)
    ·
      refine ⟨5343733639829298421527097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7124978186439064562036129 5343733639829298421527097)
      ·
        refine ⟨4007800229871973816145323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5343733639829298421527097 4007800229871973816145323)
        ·
          refine ⟨6011700344807960724217985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007800229871973816145323 6011700344807960724217985)
          ·
            refine ⟨4508775258605970543163489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6011700344807960724217985 4508775258605970543163489)
            ·
              refine ⟨3381581443954477907372617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4508775258605970543163489 3381581443954477907372617)
              ·
                refine ⟨2536186082965858430529463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381581443954477907372617 2536186082965858430529463)
                ·
                  refine ⟨3804279124448787645794195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536186082965858430529463 3804279124448787645794195)
                  ·
                    refine ⟨5706418686673181468691293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3804279124448787645794195 5706418686673181468691293)
                    ·
                      refine ⟨2139907007502443050759235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5706418686673181468691293 2139907007502443050759235)
                      ·
                        rfl

theorem cell23_4167454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4167454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167454 prefixEnd_4167454 := by exact prefixLift 4167454
  have htrace : WordTrace (prefixWord ++ tailWord_4167454) baseStart_4167454 baseEnd_4167454 := by
    simpa [prefixWord, tailWord_4167454, baseEnd_4167454] using wordTrace_append hprefix tailTrace_4167454
  have hstable : (prefixWord ++ tailWord_4167454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167454).length < 2 ^ (prefixWord ++ tailWord_4167454).sum := by decide
  have hdescent : baseEnd_4167454 < baseStart_4167454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167459 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 3]
def baseStart_4167459 : Nat := 118140960795 + 4167459 * 2 ^ 59
def prefixEnd_4167459 : Nat := 4983230072969 + 3 ^ 40 * 4167459 * 2
def baseEnd_4167459 : Nat := 2139909574905715531196711

theorem tailTrace_4167459 : CollatzResearch.WordTrace tailWord_4167459 prefixEnd_4167459 2139909574905715531196711 := by
  unfold tailWord_4167459
  simp only [CollatzResearch.WordTrace]
  refine ⟨151999717009015263177369431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101333144672676842118246287 151999717009015263177369431)
  ·
    refine ⟨227999575513522894766054147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151999717009015263177369431 227999575513522894766054147)
    ·
      refine ⟨341999363270284342149081221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227999575513522894766054147 341999363270284342149081221)
      ·
        refine ⟨64124880613178314152952729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341999363270284342149081221 64124880613178314152952729)
        ·
          refine ⟨48093660459883735614714547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64124880613178314152952729 48093660459883735614714547)
          ·
            refine ⟨72140490689825603422071821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48093660459883735614714547 72140490689825603422071821)
            ·
              refine ⟨27052684008684601283276933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72140490689825603422071821 27052684008684601283276933)
              ·
                refine ⟨5072378251628362740614425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27052684008684601283276933 5072378251628362740614425)
                ·
                  refine ⟨3804283688721272055460819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5072378251628362740614425 3804283688721272055460819)
                  ·
                    refine ⟨5706425533081908083191229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3804283688721272055460819 5706425533081908083191229)
                    ·
                      refine ⟨2139909574905715531196711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5706425533081908083191229 2139909574905715531196711)
                      ·
                        rfl

theorem cell23_4167459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_4167459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167459 prefixEnd_4167459 := by exact prefixLift 4167459
  have htrace : WordTrace (prefixWord ++ tailWord_4167459) baseStart_4167459 baseEnd_4167459 := by
    simpa [prefixWord, tailWord_4167459, baseEnd_4167459] using wordTrace_append hprefix tailTrace_4167459
  have hstable : (prefixWord ++ tailWord_4167459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167459).length < 2 ^ (prefixWord ++ tailWord_4167459).sum := by decide
  have hdescent : baseEnd_4167459 < baseStart_4167459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167460 : List Nat := [2, 3, 1, 3, 2, 1, 4, 2, 1, 2, 2]
def baseStart_4167460 : Nat := 118140960795 + 4167460 * 2 ^ 59
def prefixEnd_4167460 : Nat := 4983230072969 + 3 ^ 40 * 4167460 * 2
def baseEnd_4167460 : Nat := 2139910088386370027284207

theorem tailTrace_4167460 : CollatzResearch.WordTrace tailWord_4167460 prefixEnd_4167460 2139910088386370027284207 := by
  unfold tailWord_4167460
  simp only [CollatzResearch.WordTrace]
  refine ⟨75999876741005820174077917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101333168988007760232103889 75999876741005820174077917)
  ·
    refine ⟨28499953777877182565279219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75999876741005820174077917 28499953777877182565279219)
    ·
      refine ⟨42749930666815773847918829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28499953777877182565279219 42749930666815773847918829)
      ·
        refine ⟨16031224000055915192969561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42749930666815773847918829 16031224000055915192969561)
        ·
          refine ⟨12023418000041936394727171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16031224000055915192969561 12023418000041936394727171)
          ·
            refine ⟨18035127000062904592090757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12023418000041936394727171 18035127000062904592090757)
            ·
              refine ⟨3381586312511794611017017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18035127000062904592090757 3381586312511794611017017)
              ·
                refine ⟨2536189734383845958262763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3381586312511794611017017 2536189734383845958262763)
                ·
                  refine ⟨3804284601575768937394145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536189734383845958262763 3804284601575768937394145)
                  ·
                    refine ⟨2853213451181826703045609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3804284601575768937394145 2853213451181826703045609)
                    ·
                      refine ⟨2139910088386370027284207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2853213451181826703045609 2139910088386370027284207)
                      ·
                        rfl

theorem cell23_4167460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_4167460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167460 prefixEnd_4167460 := by exact prefixLift 4167460
  have htrace : WordTrace (prefixWord ++ tailWord_4167460) baseStart_4167460 baseEnd_4167460 := by
    simpa [prefixWord, tailWord_4167460, baseEnd_4167460] using wordTrace_append hprefix tailTrace_4167460
  have hstable : (prefixWord ++ tailWord_4167460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167460).length < 2 ^ (prefixWord ++ tailWord_4167460).sum := by decide
  have hdescent : baseEnd_4167460 < baseStart_4167460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167476 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_4167476 : Nat := 118140960795 + 4167476 * 2 ^ 59
def prefixEnd_4167476 : Nat := 4983230072969 + 3 ^ 40 * 4167476 * 2
def baseEnd_4167476 : Nat := 2139918304076841964684133

theorem tailTrace_4167476 : CollatzResearch.WordTrace tailWord_4167476 prefixEnd_4167476 2139918304076841964684133 := by
  unfold tailWord_4167476
  simp only [CollatzResearch.WordTrace]
  refine ⟨76000168524976837540369141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101333558033302450053825521 76000168524976837540369141)
  ·
    refine ⟨7125015799216578519409607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76000168524976837540369141 7125015799216578519409607)
    ·
      refine ⟨10687523698824867779114411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7125015799216578519409607 10687523698824867779114411)
      ·
        refine ⟨16031285548237301668671617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10687523698824867779114411 16031285548237301668671617)
        ·
          refine ⟨12023464161177976251503713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16031285548237301668671617 12023464161177976251503713)
          ·
            refine ⟨9017598120883482188627785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12023464161177976251503713 9017598120883482188627785)
            ·
              refine ⟨6763198590662611641470839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9017598120883482188627785 6763198590662611641470839)
              ·
                refine ⟨10144797885993917462206259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763198590662611641470839 10144797885993917462206259)
                ·
                  refine ⟨15217196828990876193309389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10144797885993917462206259 15217196828990876193309389)
                  ·
                    refine ⟨5706448810871578572491021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15217196828990876193309389 5706448810871578572491021)
                    ·
                      refine ⟨2139918304076841964684133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5706448810871578572491021 2139918304076841964684133)
                      ·
                        rfl

theorem cell23_4167476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_4167476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167476 prefixEnd_4167476 := by exact prefixLift 4167476
  have htrace : WordTrace (prefixWord ++ tailWord_4167476) baseStart_4167476 baseEnd_4167476 := by
    simpa [prefixWord, tailWord_4167476, baseEnd_4167476] using wordTrace_append hprefix tailTrace_4167476
  have hstable : (prefixWord ++ tailWord_4167476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167476).length < 2 ^ (prefixWord ++ tailWord_4167476).sum := by decide
  have hdescent : baseEnd_4167476 < baseStart_4167476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167486 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_4167486 : Nat := 118140960795 + 4167486 * 2 ^ 59
def prefixEnd_4167486 : Nat := 4983230072969 + 3 ^ 40 * 4167486 * 2
def baseEnd_4167486 : Nat := 2139923438883386925559087

theorem tailTrace_4167486 : CollatzResearch.WordTrace tailWord_4167486 prefixEnd_4167486 2139923438883386925559087 := by
  unfold tailWord_4167486
  simp only [CollatzResearch.WordTrace]
  refine ⟨19000087722489680848575289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101333801186611631192401541 19000087722489680848575289)
  ·
    refine ⟨14250065791867260636431467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19000087722489680848575289 14250065791867260636431467)
    ·
      refine ⟨21375098687800890954647201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14250065791867260636431467 21375098687800890954647201)
      ·
        refine ⟨16031324015850668215985401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21375098687800890954647201 16031324015850668215985401)
        ·
          refine ⟨12023493011888001161989051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16031324015850668215985401 12023493011888001161989051)
          ·
            refine ⟨18035239517832001742983577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12023493011888001161989051 18035239517832001742983577)
            ·
              refine ⟨13526429638374001307237683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18035239517832001742983577 13526429638374001307237683)
              ·
                refine ⟨20289644457561001960856525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13526429638374001307237683 20289644457561001960856525)
                ·
                  refine ⟨7608616671585375735321197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20289644457561001960856525 7608616671585375735321197)
                  ·
                    refine ⟨2853231251844515900745449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7608616671585375735321197 2853231251844515900745449)
                    ·
                      refine ⟨2139923438883386925559087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2853231251844515900745449 2139923438883386925559087)
                      ·
                        rfl

theorem cell23_4167486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_4167486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167486 prefixEnd_4167486 := by exact prefixLift 4167486
  have htrace : WordTrace (prefixWord ++ tailWord_4167486) baseStart_4167486 baseEnd_4167486 := by
    simpa [prefixWord, tailWord_4167486, baseEnd_4167486] using wordTrace_append hprefix tailTrace_4167486
  have hstable : (prefixWord ++ tailWord_4167486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167486).length < 2 ^ (prefixWord ++ tailWord_4167486).sum := by decide
  have hdescent : baseEnd_4167486 < baseStart_4167486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167552 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 2, 5]
def baseStart_4167552 : Nat := 118140960795 + 4167552 * 2 ^ 59
def prefixEnd_4167552 : Nat := 4983230072969 + 3 ^ 40 * 4167552 * 2
def baseEnd_4167552 : Nat := 713319109535527889111261

theorem tailTrace_4167552 : CollatzResearch.WordTrace tailWord_4167552 prefixEnd_4167552 713319109535527889111261 := by
  unfold tailWord_4167552
  simp only [CollatzResearch.WordTrace]
  refine ⟨76001554498839170030252455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101335405998452226707003273 76001554498839170030252455)
  ·
    refine ⟨114002331748258755045378683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76001554498839170030252455 114002331748258755045378683)
    ·
      refine ⟨171003497622388132568068025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114002331748258755045378683 171003497622388132568068025)
      ·
        refine ⟨128252623216791099426051019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171003497622388132568068025 128252623216791099426051019)
        ·
          refine ⟨192378934825186649139076529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128252623216791099426051019 192378934825186649139076529)
          ·
            refine ⟨144284201118889986854307397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192378934825186649139076529 144284201118889986854307397)
            ·
              refine ⟨27053287709791872535182637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144284201118889986854307397 27053287709791872535182637)
              ·
                refine ⟨10144982891171952200693489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27053287709791872535182637 10144982891171952200693489)
                ·
                  refine ⟨7608737168378964150520117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10144982891171952200693489 7608737168378964150520117)
                  ·
                    refine ⟨713319109535527889111261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7608737168378964150520117 713319109535527889111261)
                    ·
                      rfl

theorem cell23_4167552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_4167552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167552 prefixEnd_4167552 := by exact prefixLift 4167552
  have htrace : WordTrace (prefixWord ++ tailWord_4167552) baseStart_4167552 baseEnd_4167552 := by
    simpa [prefixWord, tailWord_4167552, baseEnd_4167552] using wordTrace_append hprefix tailTrace_4167552
  have hstable : (prefixWord ++ tailWord_4167552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167552).length < 2 ^ (prefixWord ++ tailWord_4167552).sum := by decide
  have hdescent : baseEnd_4167552 < baseStart_4167552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167589 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 2, 4, 2]
def baseStart_4167589 : Nat := 118140960795 + 4167589 * 2 ^ 59
def prefixEnd_4167589 : Nat := 4983230072969 + 3 ^ 40 * 4167589 * 2
def baseEnd_4167589 : Nat := 2139976327390800022571113

theorem tailTrace_4167589 : CollatzResearch.WordTrace tailWord_4167589 prefixEnd_4167589 2139976327390800022571113 := by
  unfold tailWord_4167589
  simp only [CollatzResearch.WordTrace]
  refine ⟨152004458498544295379601821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101336305665696196919734547 152004458498544295379601821)
  ·
    refine ⟨57001671936954110767350683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152004458498544295379601821 57001671936954110767350683)
    ·
      refine ⟨85502507905431166151026025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57001671936954110767350683 85502507905431166151026025)
      ·
        refine ⟨64126880929073374613269519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85502507905431166151026025 64126880929073374613269519)
        ·
          refine ⟨96190321393610061919904279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64126880929073374613269519 96190321393610061919904279)
          ·
            refine ⟨144285482090415092879856419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96190321393610061919904279 144285482090415092879856419)
            ·
              refine ⟨216428223135622639319784629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144285482090415092879856419 216428223135622639319784629)
              ·
                refine ⟨20290145918964622436229809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216428223135622639319784629 20290145918964622436229809)
                ·
                  refine ⟨15217609439223466827172357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20290145918964622436229809 15217609439223466827172357)
                  ·
                    refine ⟨2853301769854400030094817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15217609439223466827172357 2853301769854400030094817)
                    ·
                      refine ⟨2139976327390800022571113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2853301769854400030094817 2139976327390800022571113)
                      ·
                        rfl

theorem cell23_4167589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_4167589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167589 prefixEnd_4167589 := by exact prefixLift 4167589
  have htrace : WordTrace (prefixWord ++ tailWord_4167589) baseStart_4167589 baseEnd_4167589 := by
    simpa [prefixWord, tailWord_4167589, baseEnd_4167589] using wordTrace_append hprefix tailTrace_4167589
  have hstable : (prefixWord ++ tailWord_4167589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167589).length < 2 ^ (prefixWord ++ tailWord_4167589).sum := by decide
  have hdescent : baseEnd_4167589 < baseStart_4167589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167602 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_4167602 : Nat := 118140960795 + 4167602 * 2 ^ 59
def prefixEnd_4167602 : Nat := 4983230072969 + 3 ^ 40 * 4167602 * 2
def baseEnd_4167602 : Nat := 2139983002639308471708553

theorem tailTrace_4167602 : CollatzResearch.WordTrace tailWord_4167602 prefixEnd_4167602 2139983002639308471708553 := by
  unfold tailWord_4167602
  simp only [CollatzResearch.WordTrace]
  refine ⟨38001233161874299649956265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101336621764998132399883373 38001233161874299649956265)
  ·
    refine ⟨28500924871405724737467199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38001233161874299649956265 28500924871405724737467199)
    ·
      refine ⟨42751387307108587106200799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28500924871405724737467199 42751387307108587106200799)
      ·
        refine ⟨64127080960662880659301199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42751387307108587106200799 64127080960662880659301199)
        ·
          refine ⟨96190621440994320988951799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64127080960662880659301199 96190621440994320988951799)
          ·
            refine ⟨144285932161491481483427699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96190621440994320988951799 144285932161491481483427699)
            ·
              refine ⟨216428898242237222225141549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144285932161491481483427699 216428898242237222225141549)
              ·
                refine ⟨81160836840838958334428081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216428898242237222225141549 81160836840838958334428081)
                ·
                  refine ⟨60870627630629218750821061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81160836840838958334428081 60870627630629218750821061)
                  ·
                    refine ⟨11413242680742978515778949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60870627630629218750821061 11413242680742978515778949)
                    ·
                      refine ⟨2139983002639308471708553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11413242680742978515778949 2139983002639308471708553)
                      ·
                        rfl

theorem cell23_4167602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_4167602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167602 prefixEnd_4167602 := by exact prefixLift 4167602
  have htrace : WordTrace (prefixWord ++ tailWord_4167602) baseStart_4167602 baseEnd_4167602 := by
    simpa [prefixWord, tailWord_4167602, baseEnd_4167602] using wordTrace_append hprefix tailTrace_4167602
  have hstable : (prefixWord ++ tailWord_4167602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167602).length < 2 ^ (prefixWord ++ tailWord_4167602).sum := by decide
  have hdescent : baseEnd_4167602 < baseStart_4167602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167616 : List Nat := [2, 1, 1, 2, 3, 2, 2, 5, 1, 4]
def baseStart_4167616 : Nat := 118140960795 + 4167616 * 2 ^ 59
def prefixEnd_4167616 : Nat := 4983230072969 + 3 ^ 40 * 4167616 * 2
def baseEnd_4167616 : Nat := 713330063789490472311163

theorem tailTrace_4167616 : CollatzResearch.WordTrace tailWord_4167616 prefixEnd_4167616 713330063789490472311163 := by
  unfold tailWord_4167616
  simp only [CollatzResearch.WordTrace]
  refine ⟨76002721634723239495417351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101336962179630985993889801 76002721634723239495417351)
  ·
    refine ⟨114004082452084859243126027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76002721634723239495417351 114004082452084859243126027)
    ·
      refine ⟨171006123678127288864689041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114004082452084859243126027 171006123678127288864689041)
      ·
        refine ⟨128254592758595466648516781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171006123678127288864689041 128254592758595466648516781)
        ·
          refine ⟨48095472284473299993193793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128254592758595466648516781 48095472284473299993193793)
          ·
            refine ⟨36071604213354974994895345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48095472284473299993193793 36071604213354974994895345)
            ·
              refine ⟨27053703160016231246171509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36071604213354974994895345 27053703160016231246171509)
              ·
                refine ⟨2536284671251521679328579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27053703160016231246171509 2536284671251521679328579)
                ·
                  refine ⟨3804427006877282518992869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536284671251521679328579 3804427006877282518992869)
                  ·
                    refine ⟨713330063789490472311163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3804427006877282518992869 713330063789490472311163)
                    ·
                      rfl

theorem cell23_4167616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 1, 4].length) (baseStart_4167616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167616 prefixEnd_4167616 := by exact prefixLift 4167616
  have htrace : WordTrace (prefixWord ++ tailWord_4167616) baseStart_4167616 baseEnd_4167616 := by
    simpa [prefixWord, tailWord_4167616, baseEnd_4167616] using wordTrace_append hprefix tailTrace_4167616
  have hstable : (prefixWord ++ tailWord_4167616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167616).length < 2 ^ (prefixWord ++ tailWord_4167616).sum := by decide
  have hdescent : baseEnd_4167616 < baseStart_4167616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167652 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_4167652 : Nat := 118140960795 + 4167652 * 2 ^ 59
def prefixEnd_4167652 : Nat := 4983230072969 + 3 ^ 40 * 4167652 * 2
def baseEnd_4167652 : Nat := 2140008676672033276083323

theorem tailTrace_4167652 : CollatzResearch.WordTrace tailWord_4167652 prefixEnd_4167652 2140008676672033276083323 := by
  unfold tailWord_4167652
  simp only [CollatzResearch.WordTrace]
  refine ⟨76003378148658028569572605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101337837531544038092763473 76003378148658028569572605)
  ·
    refine ⟨28501266805746760713589727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76003378148658028569572605 28501266805746760713589727)
    ·
      refine ⟨42751900208620141070384591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28501266805746760713589727 42751900208620141070384591)
      ·
        refine ⟨64127850312930211605576887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42751900208620141070384591 64127850312930211605576887)
        ·
          refine ⟨96191775469395317408365331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64127850312930211605576887 96191775469395317408365331)
          ·
            refine ⟨144287663204092976112547997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96191775469395317408365331 144287663204092976112547997)
            ·
              refine ⟨54107873701534866042205499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144287663204092976112547997 54107873701534866042205499)
              ·
                refine ⟨81161810552302299063308249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54107873701534866042205499 81161810552302299063308249)
                ·
                  refine ⟨60871357914226724297481187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81161810552302299063308249 60871357914226724297481187)
                  ·
                    refine ⟨91307036871340086446221781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60871357914226724297481187 91307036871340086446221781)
                    ·
                      refine ⟨2140008676672033276083323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91307036871340086446221781 2140008676672033276083323)
                      ·
                        rfl

theorem cell23_4167652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_4167652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167652 prefixEnd_4167652 := by exact prefixLift 4167652
  have htrace : WordTrace (prefixWord ++ tailWord_4167652) baseStart_4167652 baseEnd_4167652 := by
    simpa [prefixWord, tailWord_4167652, baseEnd_4167652] using wordTrace_append hprefix tailTrace_4167652
  have hstable : (prefixWord ++ tailWord_4167652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167652).length < 2 ^ (prefixWord ++ tailWord_4167652).sum := by decide
  have hdescent : baseEnd_4167652 < baseStart_4167652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167673 : List Nat := [1, 2, 1, 3, 1, 4, 1, 5, 1, 1, 3]
def baseStart_4167673 : Nat := 118140960795 + 4167673 * 2 ^ 59
def prefixEnd_4167673 : Nat := 4983230072969 + 3 ^ 40 * 4167673 * 2
def baseEnd_4167673 : Nat := 2140019459765777693920727

theorem tailTrace_4167673 : CollatzResearch.WordTrace tailWord_4167673 prefixEnd_4167673 2140019459765777693920727 := by
  unfold tailWord_4167673
  simp only [CollatzResearch.WordTrace]
  refine ⟨152007522230239977725659673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101338348153493318483773115 152007522230239977725659673)
  ·
    refine ⟨114005641672679983294244755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152007522230239977725659673 114005641672679983294244755)
    ·
      refine ⟨171008462509019974941367133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114005641672679983294244755 171008462509019974941367133)
      ·
        refine ⟨64128173440882490603012675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171008462509019974941367133 64128173440882490603012675)
        ·
          refine ⟨96192260161323735904519013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64128173440882490603012675 96192260161323735904519013)
          ·
            refine ⟨18036048780248200482097315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96192260161323735904519013 18036048780248200482097315)
            ·
              refine ⟨27054073170372300723145973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18036048780248200482097315 27054073170372300723145973)
              ·
                refine ⟨2536319359722403192794935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27054073170372300723145973 2536319359722403192794935)
                ·
                  refine ⟨3804479039583604789192403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536319359722403192794935 3804479039583604789192403)
                  ·
                    refine ⟨5706718559375407183788605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3804479039583604789192403 5706718559375407183788605)
                    ·
                      refine ⟨2140019459765777693920727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5706718559375407183788605 2140019459765777693920727)
                      ·
                        rfl

theorem cell23_4167673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_4167673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167673 prefixEnd_4167673 := by exact prefixLift 4167673
  have htrace : WordTrace (prefixWord ++ tailWord_4167673) baseStart_4167673 baseEnd_4167673 := by
    simpa [prefixWord, tailWord_4167673, baseEnd_4167673] using wordTrace_append hprefix tailTrace_4167673
  have hstable : (prefixWord ++ tailWord_4167673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167673).length < 2 ^ (prefixWord ++ tailWord_4167673).sum := by decide
  have hdescent : baseEnd_4167673 < baseStart_4167673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167679 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 1, 8, 2]
def baseStart_4167679 : Nat := 118140960795 + 4167679 * 2 ^ 59
def prefixEnd_4167679 : Nat := 4983230072969 + 3 ^ 40 * 4167679 * 2
def baseEnd_4167679 : Nat := 2140022540649704670445699

theorem tailTrace_4167679 : CollatzResearch.WordTrace tailWord_4167679 prefixEnd_4167679 2140022540649704670445699 := by
  unfold tailWord_4167679
  simp only [CollatzResearch.WordTrace]
  refine ⟨152007741068218240750378091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101338494045478827166918727 152007741068218240750378091)
  ·
    refine ⟨228011611602327361125567137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152007741068218240750378091 228011611602327361125567137)
    ·
      refine ⟨171008708701745520844175353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228011611602327361125567137 171008708701745520844175353)
      ·
        refine ⟨128256531526309140633131515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171008708701745520844175353 128256531526309140633131515)
        ·
          refine ⟨192384797289463710949697273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128256531526309140633131515 192384797289463710949697273)
          ·
            refine ⟨144288597967097783212272955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192384797289463710949697273 144288597967097783212272955)
            ·
              refine ⟨216432896950646674818409433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144288597967097783212272955 216432896950646674818409433)
              ·
                refine ⟨162324672712985006113807075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216432896950646674818409433 162324672712985006113807075)
                ·
                  refine ⟨243487009069477509170710613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162324672712985006113807075 243487009069477509170710613)
                  ·
                    refine ⟨2853363387532939560594265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 243487009069477509170710613 2853363387532939560594265)
                    ·
                      refine ⟨2140022540649704670445699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2853363387532939560594265 2140022540649704670445699)
                      ·
                        rfl

theorem cell23_4167679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 8, 2].length) (baseStart_4167679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167679 prefixEnd_4167679 := by exact prefixLift 4167679
  have htrace : WordTrace (prefixWord ++ tailWord_4167679) baseStart_4167679 baseEnd_4167679 := by
    simpa [prefixWord, tailWord_4167679, baseEnd_4167679] using wordTrace_append hprefix tailTrace_4167679
  have hstable : (prefixWord ++ tailWord_4167679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167679).length < 2 ^ (prefixWord ++ tailWord_4167679).sum := by decide
  have hdescent : baseEnd_4167679 < baseStart_4167679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167696 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 7, 2, 2]
def baseStart_4167696 : Nat := 118140960795 + 4167696 * 2 ^ 59
def prefixEnd_4167696 : Nat := 4983230072969 + 3 ^ 40 * 4167696 * 2
def baseEnd_4167696 : Nat := 2140031269820831103933121

theorem tailTrace_4167696 : CollatzResearch.WordTrace tailWord_4167696 prefixEnd_4167696 2140031269820831103933121 := by
  unfold tailWord_4167696
  simp only [CollatzResearch.WordTrace]
  refine ⟨76004180554578326326873471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101338907406104435102497961 76004180554578326326873471)
  ·
    refine ⟨114006270831867489490310207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76004180554578326326873471 114006270831867489490310207)
    ·
      refine ⟨171009406247801234235465311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114006270831867489490310207 171009406247801234235465311)
      ·
        refine ⟨256514109371701851353197967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171009406247801234235465311 256514109371701851353197967)
        ·
          refine ⟨384771164057552777029796951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256514109371701851353197967 384771164057552777029796951)
          ·
            refine ⟨577156746086329165544695427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384771164057552777029796951 577156746086329165544695427)
            ·
              refine ⟨865735119129493748317043141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577156746086329165544695427 865735119129493748317043141)
              ·
                refine ⟨162325334836780077809445589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 865735119129493748317043141 162325334836780077809445589)
                ·
                  refine ⟨3804500035237033073658881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 162325334836780077809445589 3804500035237033073658881)
                  ·
                    refine ⟨2853375026427774805244161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3804500035237033073658881 2853375026427774805244161)
                    ·
                      refine ⟨2140031269820831103933121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2853375026427774805244161 2140031269820831103933121)
                      ·
                        rfl

theorem cell23_4167696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 2, 2].length) (baseStart_4167696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167696 prefixEnd_4167696 := by exact prefixLift 4167696
  have htrace : WordTrace (prefixWord ++ tailWord_4167696) baseStart_4167696 baseEnd_4167696 := by
    simpa [prefixWord, tailWord_4167696, baseEnd_4167696] using wordTrace_append hprefix tailTrace_4167696
  have hstable : (prefixWord ++ tailWord_4167696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167696).length < 2 ^ (prefixWord ++ tailWord_4167696).sum := by decide
  have hdescent : baseEnd_4167696 < baseStart_4167696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167699 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 3]
def baseStart_4167699 : Nat := 118140960795 + 4167699 * 2 ^ 59
def prefixEnd_4167699 : Nat := 4983230072969 + 3 ^ 40 * 4167699 * 2
def baseEnd_4167699 : Nat := 2140032810262794592195607

theorem tailTrace_4167699 : CollatzResearch.WordTrace tailWord_4167699 prefixEnd_4167699 2140032810262794592195607 := by
  unfold tailWord_4167699
  simp only [CollatzResearch.WordTrace]
  refine ⟨152008470528145784166106151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101338980352097189444070767 152008470528145784166106151)
  ·
    refine ⟨228012705792218676249159227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152008470528145784166106151 228012705792218676249159227)
    ·
      refine ⟨342019058688328014373738841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228012705792218676249159227 342019058688328014373738841)
      ·
        refine ⟨256514294016246010780304131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342019058688328014373738841 256514294016246010780304131)
        ·
          refine ⟨384771441024369016170456197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256514294016246010780304131 384771441024369016170456197)
          ·
            refine ⟨72144645192069190531960537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384771441024369016170456197 72144645192069190531960537)
            ·
              refine ⟨54108483894051892898970403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72144645192069190531960537 54108483894051892898970403)
              ·
                refine ⟨81162725841077839348455605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54108483894051892898970403 81162725841077839348455605)
                ·
                  refine ⟨7609005547601047438917713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81162725841077839348455605 7609005547601047438917713)
                  ·
                    refine ⟨5706754160700785579188285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7609005547601047438917713 5706754160700785579188285)
                    ·
                      refine ⟨2140032810262794592195607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5706754160700785579188285 2140032810262794592195607)
                      ·
                        rfl

theorem cell23_4167699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 3].length) (baseStart_4167699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167699 prefixEnd_4167699 := by exact prefixLift 4167699
  have htrace : WordTrace (prefixWord ++ tailWord_4167699) baseStart_4167699 baseEnd_4167699 := by
    simpa [prefixWord, tailWord_4167699, baseEnd_4167699] using wordTrace_append hprefix tailTrace_4167699
  have hstable : (prefixWord ++ tailWord_4167699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167699).length < 2 ^ (prefixWord ++ tailWord_4167699).sum := by decide
  have hdescent : baseEnd_4167699 < baseStart_4167699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167706 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_4167706 : Nat := 118140960795 + 4167706 * 2 ^ 59
def prefixEnd_4167706 : Nat := 4983230072969 + 3 ^ 40 * 4167706 * 2
def baseEnd_4167706 : Nat := 713345468209125354936025

theorem tailTrace_4167706 : CollatzResearch.WordTrace tailWord_4167706 prefixEnd_4167706 713345468209125354936025 := by
  unfold tailWord_4167706
  simp only [CollatzResearch.WordTrace]
  refine ⟨38002181459780106090402743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101339150559413616241073981 38002181459780106090402743)
  ·
    refine ⟨57003272189670159135604115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38002181459780106090402743 57003272189670159135604115)
    ·
      refine ⟨85504908284505238703406173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57003272189670159135604115 85504908284505238703406173)
      ·
        refine ⟨32064340606689464513777315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85504908284505238703406173 32064340606689464513777315)
        ·
          refine ⟨48096510910034196770665973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32064340606689464513777315 48096510910034196770665973)
          ·
            refine ⟨4509047897815705947249935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48096510910034196770665973 4509047897815705947249935)
            ·
              refine ⟨6763571846723558920874903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4509047897815705947249935 6763571846723558920874903)
              ·
                refine ⟨10145357770085338381312355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6763571846723558920874903 10145357770085338381312355)
                ·
                  refine ⟨15218036655128007571968533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10145357770085338381312355 15218036655128007571968533)
                  ·
                    refine ⟨713345468209125354936025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15218036655128007571968533 713345468209125354936025)
                    ·
                      rfl

theorem cell23_4167706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_4167706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167706 prefixEnd_4167706 := by exact prefixLift 4167706
  have htrace : WordTrace (prefixWord ++ tailWord_4167706) baseStart_4167706 baseEnd_4167706 := by
    simpa [prefixWord, tailWord_4167706, baseEnd_4167706] using wordTrace_append hprefix tailTrace_4167706
  have hstable : (prefixWord ++ tailWord_4167706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167706).length < 2 ^ (prefixWord ++ tailWord_4167706).sum := by decide
  have hdescent : baseEnd_4167706 < baseStart_4167706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167713 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_4167713 : Nat := 118140960795 + 4167713 * 2 ^ 59
def prefixEnd_4167713 : Nat := 4983230072969 + 3 ^ 40 * 4167713 * 2
def baseEnd_4167713 : Nat := 2140039998991957537420543

theorem tailTrace_4167713 : CollatzResearch.WordTrace tailWord_4167713 prefixEnd_4167713 2140039998991957537420543 := by
  unfold tailWord_4167713
  simp only [CollatzResearch.WordTrace]
  refine ⟨152008981150095064557115793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101339320766730043038077195 152008981150095064557115793)
  ·
    refine ⟨114006735862571298417836845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152008981150095064557115793 114006735862571298417836845)
    ·
      refine ⟨42752525948464236906688817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114006735862571298417836845 42752525948464236906688817)
      ·
        refine ⟨32064394461348177680016613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42752525948464236906688817 32064394461348177680016613)
        ·
          refine ⟨6012073961502783315003115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32064394461348177680016613 6012073961502783315003115)
          ·
            refine ⟨9018110942254174972504673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012073961502783315003115 9018110942254174972504673)
            ·
              refine ⟨6763583206690631229378505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9018110942254174972504673 6763583206690631229378505)
              ·
                refine ⟨5072687405017973422033879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6763583206690631229378505 5072687405017973422033879)
                ·
                  refine ⟨7609031107526960133050819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5072687405017973422033879 7609031107526960133050819)
                  ·
                    refine ⟨11413546661290440199576229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7609031107526960133050819 11413546661290440199576229)
                    ·
                      refine ⟨2140039998991957537420543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11413546661290440199576229 2140039998991957537420543)
                      ·
                        rfl

theorem cell23_4167713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_4167713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167713 prefixEnd_4167713 := by exact prefixLift 4167713
  have htrace : WordTrace (prefixWord ++ tailWord_4167713) baseStart_4167713 baseEnd_4167713 := by
    simpa [prefixWord, tailWord_4167713, baseEnd_4167713] using wordTrace_append hprefix tailTrace_4167713
  have hstable : (prefixWord ++ tailWord_4167713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167713).length < 2 ^ (prefixWord ++ tailWord_4167713).sum := by decide
  have hdescent : baseEnd_4167713 < baseStart_4167713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167736 : List Nat := [2, 1, 2, 1, 7, 1, 9]
def baseStart_4167736 : Nat := 118140960795 + 4167736 * 2 ^ 59
def prefixEnd_4167736 : Nat := 4983230072969 + 3 ^ 40 * 4167736 * 2
def baseEnd_4167736 : Nat := 26420392704284085770777

theorem tailTrace_4167736 : CollatzResearch.WordTrace tailWord_4167736 prefixEnd_4167736 26420392704284085770777 := by
  unfold tailWord_4167736
  simp only [CollatzResearch.WordTrace]
  refine ⟨76004910014505869742601531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101339880019341159656802041 76004910014505869742601531)
  ·
    refine ⟨114007365021758804613902297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76004910014505869742601531 114007365021758804613902297)
    ·
      refine ⟨85505523766319103460426723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114007365021758804613902297 85505523766319103460426723)
      ·
        refine ⟨128258285649478655190640085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85505523766319103460426723 128258285649478655190640085)
        ·
          refine ⟨3006053569909655981030627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 128258285649478655190640085 3006053569909655981030627)
          ·
            refine ⟨4509080354864483971545941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006053569909655981030627 4509080354864483971545941)
            ·
              refine ⟨26420392704284085770777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4509080354864483971545941 26420392704284085770777)
              ·
                rfl

theorem cell23_4167736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 9].length) (baseStart_4167736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167736 prefixEnd_4167736 := by exact prefixLift 4167736
  have htrace : WordTrace (prefixWord ++ tailWord_4167736) baseStart_4167736 baseEnd_4167736 := by
    simpa [prefixWord, tailWord_4167736, baseEnd_4167736] using wordTrace_append hprefix tailTrace_4167736
  have hstable : (prefixWord ++ tailWord_4167736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167736).length < 2 ^ (prefixWord ++ tailWord_4167736).sum := by decide
  have hdescent : baseEnd_4167736 < baseStart_4167736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167816 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4167816 : Nat := 118140960795 + 4167816 * 2 ^ 59
def prefixEnd_4167816 : Nat := 4983230072969 + 3 ^ 40 * 4167816 * 2
def baseEnd_4167816 : Nat := 2140092887499370634432569

theorem tailTrace_4167816 : CollatzResearch.WordTrace tailWord_4167816 prefixEnd_4167816 2140092887499370634432569 := by
  unfold tailWord_4167816
  simp only [CollatzResearch.WordTrace]
  refine ⟨76006368934360956574057651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101341825245814608765410201 76006368934360956574057651)
  ·
    refine ⟨114009553401541434861086477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76006368934360956574057651 114009553401541434861086477)
    ·
      refine ⟨42753582525578038072907429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114009553401541434861086477 42753582525578038072907429)
      ·
        refine ⟨8016296723545882138670143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42753582525578038072907429 8016296723545882138670143)
        ·
          refine ⟨12024445085318823208005215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8016296723545882138670143 12024445085318823208005215)
          ·
            refine ⟨18036667627978234812007823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024445085318823208005215 18036667627978234812007823)
            ·
              refine ⟨27055001441967352218011735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18036667627978234812007823 27055001441967352218011735)
              ·
                refine ⟨40582502162951028327017603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27055001441967352218011735 40582502162951028327017603)
                ·
                  refine ⟨60873753244426542490526405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40582502162951028327017603 60873753244426542490526405)
                  ·
                    refine ⟨11413828733329976716973701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60873753244426542490526405 11413828733329976716973701)
                    ·
                      refine ⟨2140092887499370634432569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11413828733329976716973701 2140092887499370634432569)
                      ·
                        rfl

theorem cell23_4167816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4167816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167816 prefixEnd_4167816 := by exact prefixLift 4167816
  have htrace : WordTrace (prefixWord ++ tailWord_4167816) baseStart_4167816 baseEnd_4167816 := by
    simpa [prefixWord, tailWord_4167816, baseEnd_4167816] using wordTrace_append hprefix tailTrace_4167816
  have hstable : (prefixWord ++ tailWord_4167816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167816).length < 2 ^ (prefixWord ++ tailWord_4167816).sum := by decide
  have hdescent : baseEnd_4167816 < baseStart_4167816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167826 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 7]
def baseStart_4167826 : Nat := 118140960795 + 4167826 * 2 ^ 59
def prefixEnd_4167826 : Nat := 4983230072969 + 3 ^ 40 * 4167826 * 2
def baseEnd_4167826 : Nat := 237788669145101732811947

theorem tailTrace_4167826 : CollatzResearch.WordTrace tailWord_4167826 prefixEnd_4167826 237788669145101732811947 := by
  unfold tailWord_4167826
  simp only [CollatzResearch.WordTrace]
  refine ⟨38003275649671421213994833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101342068399123789903986221 38003275649671421213994833)
  ·
    refine ⟨28502456737253565910496125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38003275649671421213994833 28502456737253565910496125)
    ·
      refine ⟨10688421276470087216436047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28502456737253565910496125 10688421276470087216436047)
      ·
        refine ⟨16032631914705130824654071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10688421276470087216436047 16032631914705130824654071)
        ·
          refine ⟨24048947872057696236981107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16032631914705130824654071 24048947872057696236981107)
          ·
            refine ⟨36073421808086544355471661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24048947872057696236981107 36073421808086544355471661)
            ·
              refine ⟨13527533178032454133301873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36073421808086544355471661 13527533178032454133301873)
              ·
                refine ⟨10145649883524340599976405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13527533178032454133301873 10145649883524340599976405)
                ·
                  refine ⟨237788669145101732811947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10145649883524340599976405 237788669145101732811947)
                  ·
                    rfl

theorem cell23_4167826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_4167826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167826 prefixEnd_4167826 := by exact prefixLift 4167826
  have htrace : WordTrace (prefixWord ++ tailWord_4167826) baseStart_4167826 baseEnd_4167826 := by
    simpa [prefixWord, tailWord_4167826, baseEnd_4167826] using wordTrace_append hprefix tailTrace_4167826
  have hstable : (prefixWord ++ tailWord_4167826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167826).length < 2 ^ (prefixWord ++ tailWord_4167826).sum := by decide
  have hdescent : baseEnd_4167826 < baseStart_4167826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167836 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_4167836 : Nat := 118140960795 + 4167836 * 2 ^ 59
def prefixEnd_4167836 : Nat := 4983230072969 + 3 ^ 40 * 4167836 * 2
def baseEnd_4167836 : Nat := 2140103157112460556182477

theorem tailTrace_4167836 : CollatzResearch.WordTrace tailWord_4167836 prefixEnd_4167836 2140103157112460556182477 := by
  unfold tailWord_4167836
  simp only [CollatzResearch.WordTrace]
  refine ⟨76006733664324728281921681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101342311552432971042562241 76006733664324728281921681)
  ·
    refine ⟨57005050248243546211441261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76006733664324728281921681 57005050248243546211441261)
    ·
      refine ⟨21376893843091329829290473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57005050248243546211441261 21376893843091329829290473)
      ·
        refine ⟨16032670382318497371967855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21376893843091329829290473 16032670382318497371967855)
        ·
          refine ⟨24049005573477746057951783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16032670382318497371967855 24049005573477746057951783)
          ·
            refine ⟨36073508360216619086927675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24049005573477746057951783 36073508360216619086927675)
            ·
              refine ⟨54110262540324928630391513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36073508360216619086927675 54110262540324928630391513)
              ·
                refine ⟨40582696905243696472793635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54110262540324928630391513 40582696905243696472793635)
                ·
                  refine ⟨60874045357865544709190453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40582696905243696472793635 60874045357865544709190453)
                  ·
                    refine ⟨5706941752299894816486605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60874045357865544709190453 5706941752299894816486605)
                    ·
                      refine ⟨2140103157112460556182477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5706941752299894816486605 2140103157112460556182477)
                      ·
                        rfl

theorem cell23_4167836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_4167836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167836 prefixEnd_4167836 := by exact prefixLift 4167836
  have htrace : WordTrace (prefixWord ++ tailWord_4167836) baseStart_4167836 baseEnd_4167836 := by
    simpa [prefixWord, tailWord_4167836, baseEnd_4167836] using wordTrace_append hprefix tailTrace_4167836
  have hstable : (prefixWord ++ tailWord_4167836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167836).length < 2 ^ (prefixWord ++ tailWord_4167836).sum := by decide
  have hdescent : baseEnd_4167836 < baseStart_4167836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167853 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_4167853 : Nat := 118140960795 + 4167853 * 2 ^ 59
def prefixEnd_4167853 : Nat := 4983230072969 + 3 ^ 40 * 4167853 * 2
def baseEnd_4167853 : Nat := 2140111886283586989669899

theorem tailTrace_4167853 : CollatzResearch.WordTrace tailWord_4167853 prefixEnd_4167853 2140111886283586989669899 := by
  unfold tailWord_4167853
  simp only [CollatzResearch.WordTrace]
  refine ⟨152014087369587868467212213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101342724913058578978141475 152014087369587868467212213)
  ·
    refine ⟨14251320690898862668801145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152014087369587868467212213 14251320690898862668801145)
    ·
      refine ⟨10688490518174147001600859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14251320690898862668801145 10688490518174147001600859)
      ·
        refine ⟨16032735777261220502401289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10688490518174147001600859 16032735777261220502401289)
        ·
          refine ⟨12024551832945915376800967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16032735777261220502401289 12024551832945915376800967)
          ·
            refine ⟨18036827749418873065201451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024551832945915376800967 18036827749418873065201451)
            ·
              refine ⟨27055241624128309597802177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18036827749418873065201451 27055241624128309597802177)
              ·
                refine ⟨20291431218096232198351633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27055241624128309597802177 20291431218096232198351633)
                ·
                  refine ⟨15218573413572174148763725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20291431218096232198351633 15218573413572174148763725)
                  ·
                    refine ⟨5706965030089565305786397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15218573413572174148763725 5706965030089565305786397)
                    ·
                      refine ⟨2140111886283586989669899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5706965030089565305786397 2140111886283586989669899)
                      ·
                        rfl

theorem cell23_4167853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_4167853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167853 prefixEnd_4167853 := by exact prefixLift 4167853
  have htrace : WordTrace (prefixWord ++ tailWord_4167853) baseStart_4167853 baseEnd_4167853 := by
    simpa [prefixWord, tailWord_4167853, baseEnd_4167853] using wordTrace_append hprefix tailTrace_4167853
  have hstable : (prefixWord ++ tailWord_4167853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167853).length < 2 ^ (prefixWord ++ tailWord_4167853).sum := by decide
  have hdescent : baseEnd_4167853 < baseStart_4167853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167854 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4167854 : Nat := 118140960795 + 4167854 * 2 ^ 59
def prefixEnd_4167854 : Nat := 4983230072969 + 3 ^ 40 * 4167854 * 2
def baseEnd_4167854 : Nat := 2140112399764241485757395

theorem tailTrace_4167854 : CollatzResearch.WordTrace tailWord_4167854 prefixEnd_4167854 2140112399764241485757395 := by
  unfold tailWord_4167854
  simp only [CollatzResearch.WordTrace]
  refine ⟨19001765480323030704749827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101342749228389497091999077 19001765480323030704749827)
  ·
    refine ⟨28502648220484546057124741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19001765480323030704749827 28502648220484546057124741)
    ·
      refine ⟨5344246541340852385710889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28502648220484546057124741 5344246541340852385710889)
      ·
        refine ⟨4008184906005639289283167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5344246541340852385710889 4008184906005639289283167)
        ·
          refine ⟨6012277359008458933924751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008184906005639289283167 6012277359008458933924751)
          ·
            refine ⟨9018416038512688400887127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012277359008458933924751 9018416038512688400887127)
            ·
              refine ⟨13527624057769032601330691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9018416038512688400887127 13527624057769032601330691)
              ·
                refine ⟨20291436086653548901996037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13527624057769032601330691 20291436086653548901996037)
                ·
                  refine ⟨3804644266247540419124257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20291436086653548901996037 3804644266247540419124257)
                  ·
                    refine ⟨2853483199685655314343193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3804644266247540419124257 2853483199685655314343193)
                    ·
                      refine ⟨2140112399764241485757395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2853483199685655314343193 2140112399764241485757395)
                      ·
                        rfl

theorem cell23_4167854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4167854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167854 prefixEnd_4167854 := by exact prefixLift 4167854
  have htrace : WordTrace (prefixWord ++ tailWord_4167854) baseStart_4167854 baseEnd_4167854 := by
    simpa [prefixWord, tailWord_4167854, baseEnd_4167854] using wordTrace_append hprefix tailTrace_4167854
  have hstable : (prefixWord ++ tailWord_4167854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167854).length < 2 ^ (prefixWord ++ tailWord_4167854).sum := by decide
  have hdescent : baseEnd_4167854 < baseStart_4167854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167899 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 8]
def baseStart_4167899 : Nat := 118140960795 + 4167899 * 2 ^ 59
def prefixEnd_4167899 : Nat := 4983230072969 + 3 ^ 40 * 4167899 * 2
def baseEnd_4167899 : Nat := 237792834043743756632743

theorem tailTrace_4167899 : CollatzResearch.WordTrace tailWord_4167899 prefixEnd_4167899 237792834043743756632743 := by
  unfold tailWord_4167899
  simp only [CollatzResearch.WordTrace]
  refine ⟨152015765127421218323386751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101343843418280812215591167 152015765127421218323386751)
  ·
    refine ⟨228023647691131827485080127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152015765127421218323386751 228023647691131827485080127)
    ·
      refine ⟨342035471536697741227620191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228023647691131827485080127 342035471536697741227620191)
      ·
        refine ⟨513053207305046611841430287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342035471536697741227620191 513053207305046611841430287)
        ·
          refine ⟨769579810957569917762145431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513053207305046611841430287 769579810957569917762145431)
          ·
            refine ⟨1154369716436354876643218147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769579810957569917762145431 1154369716436354876643218147)
            ·
              refine ⟨1731554574654532314964827221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154369716436354876643218147 1731554574654532314964827221)
              ·
                refine ⟨20291655171732800565994069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1731554574654532314964827221 20291655171732800565994069)
                ·
                  refine ⟨237792834043743756632743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20291655171732800565994069 237792834043743756632743)
                  ·
                    rfl

theorem cell23_4167899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 8].length) (baseStart_4167899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167899 prefixEnd_4167899 := by exact prefixLift 4167899
  have htrace : WordTrace (prefixWord ++ tailWord_4167899) baseStart_4167899 baseEnd_4167899 := by
    simpa [prefixWord, tailWord_4167899, baseEnd_4167899] using wordTrace_append hprefix tailTrace_4167899
  have hstable : (prefixWord ++ tailWord_4167899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167899).length < 2 ^ (prefixWord ++ tailWord_4167899).sum := by decide
  have hdescent : baseEnd_4167899 < baseStart_4167899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167916 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 6]
def baseStart_4167916 : Nat := 118140960795 + 4167916 * 2 ^ 59
def prefixEnd_4167916 : Nat := 4983230072969 + 3 ^ 40 * 4167916 * 2
def baseEnd_4167916 : Nat := 237793803951646693686901

theorem tailTrace_4167916 : CollatzResearch.WordTrace tailWord_4167916 prefixEnd_4167916 237793803951646693686901 := by
  unfold tailWord_4167916
  simp only [CollatzResearch.WordTrace]
  refine ⟨76008192584179815113377801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101344256778906420151170401 76008192584179815113377801)
  ·
    refine ⟨57006144438134861335033351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76008192584179815113377801 57006144438134861335033351)
    ·
      refine ⟨85509216657202292002550027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57006144438134861335033351 85509216657202292002550027)
      ·
        refine ⟨128263824985803438003825041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85509216657202292002550027 128263824985803438003825041)
        ·
          refine ⟨96197868739352578502868781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128263824985803438003825041 96197868739352578502868781)
          ·
            refine ⟨36074200777257216938575793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96197868739352578502868781 36074200777257216938575793)
            ·
              refine ⟨27055650582942912703931845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36074200777257216938575793 27055650582942912703931845)
              ·
                refine ⟨5072934484301796131987221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27055650582942912703931845 5072934484301796131987221)
                ·
                  refine ⟨237793803951646693686901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5072934484301796131987221 237793803951646693686901)
                  ·
                    rfl

theorem cell23_4167916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_4167916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167916 prefixEnd_4167916 := by exact prefixLift 4167916
  have htrace : WordTrace (prefixWord ++ tailWord_4167916) baseStart_4167916 baseEnd_4167916 := by
    simpa [prefixWord, tailWord_4167916, baseEnd_4167916] using wordTrace_append hprefix tailTrace_4167916
  have hstable : (prefixWord ++ tailWord_4167916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167916).length < 2 ^ (prefixWord ++ tailWord_4167916).sum := by decide
  have hdescent : baseEnd_4167916 < baseStart_4167916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4167993 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 1, 6]
def baseStart_4167993 : Nat := 118140960795 + 4167993 * 2 ^ 59
def prefixEnd_4167993 : Nat := 4983230072969 + 3 ^ 40 * 4167993 * 2
def baseEnd_4167993 : Nat := 713394591191738813973085

theorem tailTrace_4167993 : CollatzResearch.WordTrace tailWord_4167993 prefixEnd_4167993 713394591191738813973085 := by
  unfold tailWord_4167993
  simp only [CollatzResearch.WordTrace]
  refine ⟨152019193589080672377308633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101346129059387114918205755 152019193589080672377308633)
  ·
    refine ⟨114014395191810504282981475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152019193589080672377308633 114014395191810504282981475)
    ·
      refine ⟨171021592787715756424472213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114014395191810504282981475 171021592787715756424472213)
      ·
        refine ⟨8016637161924176082397135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 171021592787715756424472213 8016637161924176082397135)
        ·
          refine ⟨12024955742886264123595703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8016637161924176082397135 12024955742886264123595703)
          ·
            refine ⟨18037433614329396185393555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12024955742886264123595703 18037433614329396185393555)
            ·
              refine ⟨27056150421494094278090333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18037433614329396185393555 27056150421494094278090333)
              ·
                refine ⟨10146056408060285354283875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27056150421494094278090333 10146056408060285354283875)
                ·
                  refine ⟨15219084612090428031425813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10146056408060285354283875 15219084612090428031425813)
                  ·
                    refine ⟨713394591191738813973085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15219084612090428031425813 713394591191738813973085)
                    ·
                      rfl

theorem cell23_4167993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_4167993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4167993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4167993 prefixEnd_4167993 := by exact prefixLift 4167993
  have htrace : WordTrace (prefixWord ++ tailWord_4167993) baseStart_4167993 baseEnd_4167993 := by
    simpa [prefixWord, tailWord_4167993, baseEnd_4167993] using wordTrace_append hprefix tailTrace_4167993
  have hstable : (prefixWord ++ tailWord_4167993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4167993).length < 2 ^ (prefixWord ++ tailWord_4167993).sum := by decide
  have hdescent : baseEnd_4167993 < baseStart_4167993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4167993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168003 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 3]
def baseStart_4168003 : Nat := 118140960795 + 4168003 * 2 ^ 59
def prefixEnd_4168003 : Nat := 4983230072969 + 3 ^ 40 * 4168003 * 2
def baseEnd_4168003 : Nat := 2140188908381761402794209

theorem tailTrace_4168003 : CollatzResearch.WordTrace tailWord_4168003 prefixEnd_4168003 2140188908381761402794209 := by
  unfold tailWord_4168003
  simp only [CollatzResearch.WordTrace]
  refine ⟨152019558319044444085172663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101346372212696296056781775 152019558319044444085172663)
  ·
    refine ⟨228029337478566666127758995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152019558319044444085172663 228029337478566666127758995)
    ·
      refine ⟨342044006217849999191638493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228029337478566666127758995 342044006217849999191638493)
      ·
        refine ⟨128266502331693749696864435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342044006217849999191638493 128266502331693749696864435)
        ·
          refine ⟨192399753497540624545296653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128266502331693749696864435 192399753497540624545296653)
          ·
            refine ⟨72149907561577734204486245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192399753497540624545296653 72149907561577734204486245)
            ·
              refine ⟨13528107667795825163341171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72149907561577734204486245 13528107667795825163341171)
              ·
                refine ⟨20292161501693737745011757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13528107667795825163341171 20292161501693737745011757)
                ·
                  refine ⟨7609560563135151654379409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20292161501693737745011757 7609560563135151654379409)
                  ·
                    refine ⟨5707170422351363740784557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7609560563135151654379409 5707170422351363740784557)
                    ·
                      refine ⟨2140188908381761402794209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707170422351363740784557 2140188908381761402794209)
                      ·
                        rfl

theorem cell23_4168003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_4168003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168003 prefixEnd_4168003 := by exact prefixLift 4168003
  have htrace : WordTrace (prefixWord ++ tailWord_4168003) baseStart_4168003 baseEnd_4168003 := by
    simpa [prefixWord, tailWord_4168003, baseEnd_4168003] using wordTrace_append hprefix tailTrace_4168003
  have hstable : (prefixWord ++ tailWord_4168003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168003).length < 2 ^ (prefixWord ++ tailWord_4168003).sum := by decide
  have hdescent : baseEnd_4168003 < baseStart_4168003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168017 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 1, 1, 4]
def baseStart_4168017 : Nat := 118140960795 + 4168017 * 2 ^ 59
def prefixEnd_4168017 : Nat := 4983230072969 + 3 ^ 40 * 4168017 * 2
def baseEnd_4168017 : Nat := 2140196097110924348019145

theorem tailTrace_4168017 : CollatzResearch.WordTrace tailWord_4168017 prefixEnd_4168017 2140196097110924348019145 := by
  unfold tailWord_4168017
  simp only [CollatzResearch.WordTrace]
  refine ⟨152020068940993724476182305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101346712627329149650788203 152020068940993724476182305)
  ·
    refine ⟨114015051705745293357136729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152020068940993724476182305 114015051705745293357136729)
    ·
      refine ⟨85511288779308970017852547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114015051705745293357136729 85511288779308970017852547)
      ·
        refine ⟨128266933168963455026778821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85511288779308970017852547 128266933168963455026778821)
        ·
          refine ⟨24050049969180647817521029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128266933168963455026778821 24050049969180647817521029)
          ·
            refine ⟨4509384369221371465785193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24050049969180647817521029 4509384369221371465785193)
            ·
              refine ⟨3382038276916028599338895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4509384369221371465785193 3382038276916028599338895)
              ·
                refine ⟨5073057415374042899008343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3382038276916028599338895 5073057415374042899008343)
                ·
                  refine ⟨7609586123061064348512515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5073057415374042899008343 7609586123061064348512515)
                  ·
                    refine ⟨11414379184591596522768773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7609586123061064348512515 11414379184591596522768773)
                    ·
                      refine ⟨2140196097110924348019145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11414379184591596522768773 2140196097110924348019145)
                      ·
                        rfl

theorem cell23_4168017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_4168017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168017 prefixEnd_4168017 := by exact prefixLift 4168017
  have htrace : WordTrace (prefixWord ++ tailWord_4168017) baseStart_4168017 baseEnd_4168017 := by
    simpa [prefixWord, tailWord_4168017, baseEnd_4168017] using wordTrace_append hprefix tailTrace_4168017
  have hstable : (prefixWord ++ tailWord_4168017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168017).length < 2 ^ (prefixWord ++ tailWord_4168017).sum := by decide
  have hdescent : baseEnd_4168017 < baseStart_4168017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168026 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_4168026 : Nat := 118140960795 + 4168026 * 2 ^ 59
def prefixEnd_4168026 : Nat := 4983230072969 + 3 ^ 40 * 4168026 * 2
def baseEnd_4168026 : Nat := 2140200718436814812806603

theorem tailTrace_4168026 : CollatzResearch.WordTrace tailWord_4168026 prefixEnd_4168026 2140200718436814812806603 := by
  unfold tailWord_4168026
  simp only [CollatzResearch.WordTrace]
  refine ⟨38005099299490279753314983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101346931465307412675506621 38005099299490279753314983)
  ·
    refine ⟨57007648949235419629972475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38005099299490279753314983 57007648949235419629972475)
    ·
      refine ⟨85511473423853129444958713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57007648949235419629972475 85511473423853129444958713)
      ·
        refine ⟨64133605067889847083719035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85511473423853129444958713 64133605067889847083719035)
        ·
          refine ⟨96200407601834770625578553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64133605067889847083719035 96200407601834770625578553)
          ·
            refine ⟨72150305701376077969183915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96200407601834770625578553 72150305701376077969183915)
            ·
              refine ⟨108225458552064116953775873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72150305701376077969183915 108225458552064116953775873)
              ·
                refine ⟨81169093914048087715331905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108225458552064116953775873 81169093914048087715331905)
                ·
                  refine ⟨60876820435536065786498929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81169093914048087715331905 60876820435536065786498929)
                  ·
                    refine ⟨45657615326652049339874197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60876820435536065786498929 45657615326652049339874197)
                    ·
                      refine ⟨2140200718436814812806603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45657615326652049339874197 2140200718436814812806603)
                      ·
                        rfl

theorem cell23_4168026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_4168026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168026 prefixEnd_4168026 := by exact prefixLift 4168026
  have htrace : WordTrace (prefixWord ++ tailWord_4168026) baseStart_4168026 baseEnd_4168026 := by
    simpa [prefixWord, tailWord_4168026, baseEnd_4168026] using wordTrace_append hprefix tailTrace_4168026
  have hstable : (prefixWord ++ tailWord_4168026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168026).length < 2 ^ (prefixWord ++ tailWord_4168026).sum := by decide
  have hdescent : baseEnd_4168026 < baseStart_4168026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168034 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_4168034 : Nat := 118140960795 + 4168034 * 2 ^ 59
def prefixEnd_4168034 : Nat := 4983230072969 + 3 ^ 40 * 4168034 * 2
def baseEnd_4168034 : Nat := 2140204826282050781506567

theorem tailTrace_4168034 : CollatzResearch.WordTrace tailWord_4168034 prefixEnd_4168034 2140204826282050781506567 := by
  unfold tailWord_4168034
  simp only [CollatzResearch.WordTrace]
  refine ⟨38005172245483034094887789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101347125987954757586367437 38005172245483034094887789)
  ·
    refine ⟨14251939592056137785582921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38005172245483034094887789 14251939592056137785582921)
    ·
      refine ⟨10688954694042103339187191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14251939592056137785582921 10688954694042103339187191)
      ·
        refine ⟨16033432041063155008780787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10688954694042103339187191 16033432041063155008780787)
        ·
          refine ⟨24050148061594732513171181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16033432041063155008780787 24050148061594732513171181)
          ·
            refine ⟨9018805523098024692439193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24050148061594732513171181 9018805523098024692439193)
            ·
              refine ⟨6764104142323518519329395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9018805523098024692439193 6764104142323518519329395)
              ·
                refine ⟨10146156213485277778994093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764104142323518519329395 10146156213485277778994093)
                ·
                  refine ⟨3804808580056979167122785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10146156213485277778994093 3804808580056979167122785)
                  ·
                    refine ⟨2853606435042734375342089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3804808580056979167122785 2853606435042734375342089)
                    ·
                      refine ⟨2140204826282050781506567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2853606435042734375342089 2140204826282050781506567)
                      ·
                        rfl

theorem cell23_4168034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_4168034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168034 prefixEnd_4168034 := by exact prefixLift 4168034
  have htrace : WordTrace (prefixWord ++ tailWord_4168034) baseStart_4168034 baseEnd_4168034 := by
    simpa [prefixWord, tailWord_4168034, baseEnd_4168034] using wordTrace_append hprefix tailTrace_4168034
  have hstable : (prefixWord ++ tailWord_4168034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168034).length < 2 ^ (prefixWord ++ tailWord_4168034).sum := by decide
  have hdescent : baseEnd_4168034 < baseStart_4168034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168050 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_4168050 : Nat := 118140960795 + 4168050 * 2 ^ 59
def prefixEnd_4168050 : Nat := 4983230072969 + 3 ^ 40 * 4168050 * 2
def baseEnd_4168050 : Nat := 2140213041972522718906493

theorem tailTrace_4168050 : CollatzResearch.WordTrace tailWord_4168050 prefixEnd_4168050 2140213041972522718906493 := by
  unfold tailWord_4168050
  simp only [CollatzResearch.WordTrace]
  refine ⟨38005318137468542778033401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101347515033249447408089069 38005318137468542778033401)
  ·
    refine ⟨28503988603101407083525051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38005318137468542778033401 28503988603101407083525051)
    ·
      refine ⟨42755982904652110625287577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28503988603101407083525051 42755982904652110625287577)
      ·
        refine ⟨32066987178489082968965683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42755982904652110625287577 32066987178489082968965683)
        ·
          refine ⟨48100480767733624453448525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32066987178489082968965683 48100480767733624453448525)
          ·
            refine ⟨18037680287900109170043197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48100480767733624453448525 18037680287900109170043197)
            ·
              refine ⟨6764130107962540938766199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18037680287900109170043197 6764130107962540938766199)
              ·
                refine ⟨10146195161943811408149299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6764130107962540938766199 10146195161943811408149299)
                ·
                  refine ⟨15219292742915717112223949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10146195161943811408149299 15219292742915717112223949)
                  ·
                    refine ⟨5707234778593393917083981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15219292742915717112223949 5707234778593393917083981)
                    ·
                      refine ⟨2140213041972522718906493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707234778593393917083981 2140213041972522718906493)
                      ·
                        rfl

theorem cell23_4168050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_4168050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168050 prefixEnd_4168050 := by exact prefixLift 4168050
  have htrace : WordTrace (prefixWord ++ tailWord_4168050) baseStart_4168050 baseEnd_4168050 := by
    simpa [prefixWord, tailWord_4168050, baseEnd_4168050] using wordTrace_append hprefix tailTrace_4168050
  have hstable : (prefixWord ++ tailWord_4168050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168050).length < 2 ^ (prefixWord ++ tailWord_4168050).sum := by decide
  have hdescent : baseEnd_4168050 < baseStart_4168050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168153 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_4168153 : Nat := 118140960795 + 4168153 * 2 ^ 59
def prefixEnd_4168153 : Nat := 4983230072969 + 3 ^ 40 * 4168153 * 2
def baseEnd_4168153 : Nat := 2140265930479935815918519

theorem tailTrace_4168153 : CollatzResearch.WordTrace tailWord_4168153 prefixEnd_4168153 2140265930479935815918519 := by
  unfold tailWord_4168153
  simp only [CollatzResearch.WordTrace]
  refine ⟨152025029268501019703133113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101350019512334013135422075 152025029268501019703133113)
  ·
    refine ⟨114018771951375764777349835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152025029268501019703133113 114018771951375764777349835)
    ·
      refine ⟨171028157927063647166024753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114018771951375764777349835 171028157927063647166024753)
      ·
        refine ⟨128271118445297735374518565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171028157927063647166024753 128271118445297735374518565)
        ·
          refine ⟨24050834708493325382722231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128271118445297735374518565 24050834708493325382722231)
          ·
            refine ⟨36076252062739988074083347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24050834708493325382722231 36076252062739988074083347)
            ·
              refine ⟨54114378094109982111125021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36076252062739988074083347 54114378094109982111125021)
              ·
                refine ⟨20292891785291243291671883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54114378094109982111125021 20292891785291243291671883)
                ·
                  refine ⟨30439337677936864937507825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20292891785291243291671883 30439337677936864937507825)
                  ·
                    refine ⟨22829503258452648703130869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30439337677936864937507825 22829503258452648703130869)
                    ·
                      refine ⟨2140265930479935815918519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22829503258452648703130869 2140265930479935815918519)
                      ·
                        rfl

theorem cell23_4168153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_4168153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168153 prefixEnd_4168153 := by exact prefixLift 4168153
  have htrace : WordTrace (prefixWord ++ tailWord_4168153) baseStart_4168153 baseEnd_4168153 := by
    simpa [prefixWord, tailWord_4168153, baseEnd_4168153] using wordTrace_append hprefix tailTrace_4168153
  have hstable : (prefixWord ++ tailWord_4168153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168153).length < 2 ^ (prefixWord ++ tailWord_4168153).sum := by decide
  have hdescent : baseEnd_4168153 < baseStart_4168153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168200 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_4168200 : Nat := 118140960795 + 4168200 * 2 ^ 59
def prefixEnd_4168200 : Nat := 4983230072969 + 3 ^ 40 * 4168200 * 2
def baseEnd_4168200 : Nat := 2140290064070697132030803

theorem tailTrace_4168200 : CollatzResearch.WordTrace tailWord_4168200 prefixEnd_4168200 2140290064070697132030803 := by
  unfold tailWord_4168200
  simp only [CollatzResearch.WordTrace]
  refine ⟨76013371749665373365047027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101351162332887164486729369 76013371749665373365047027)
  ·
    refine ⟨114020057624498060047570541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76013371749665373365047027 114020057624498060047570541)
    ·
      refine ⟨42757521609186772517838953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114020057624498060047570541 42757521609186772517838953)
      ·
        refine ⟨32068141206890079388379215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42757521609186772517838953 32068141206890079388379215)
        ·
          refine ⟨48102211810335119082568823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32068141206890079388379215 48102211810335119082568823)
          ·
            refine ⟨72153317715502678623853235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48102211810335119082568823 72153317715502678623853235)
            ·
              refine ⟨108229976573254017935779853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72153317715502678623853235 108229976573254017935779853)
              ·
                refine ⟨40586241214970256725917445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108229976573254017935779853 40586241214970256725917445)
                ·
                  refine ⟨7609920227806923136109521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40586241214970256725917445 7609920227806923136109521)
                  ·
                    refine ⟨5707440170855192352082141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7609920227806923136109521 5707440170855192352082141)
                    ·
                      refine ⟨2140290064070697132030803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707440170855192352082141 2140290064070697132030803)
                      ·
                        rfl

theorem cell23_4168200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_4168200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168200 prefixEnd_4168200 := by exact prefixLift 4168200
  have htrace : WordTrace (prefixWord ++ tailWord_4168200) baseStart_4168200 baseEnd_4168200 := by
    simpa [prefixWord, tailWord_4168200, baseEnd_4168200] using wordTrace_append hprefix tailTrace_4168200
  have hstable : (prefixWord ++ tailWord_4168200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168200).length < 2 ^ (prefixWord ++ tailWord_4168200).sum := by decide
  have hdescent : baseEnd_4168200 < baseStart_4168200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168223 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_4168223 : Nat := 118140960795 + 4168223 * 2 ^ 59
def prefixEnd_4168223 : Nat := 4983230072969 + 3 ^ 40 * 4168223 * 2
def baseEnd_4168223 : Nat := 2140301874125750542043197

theorem tailTrace_4168223 : CollatzResearch.WordTrace tailWord_4168223 prefixEnd_4168223 2140301874125750542043197 := by
  unfold tailWord_4168223
  simp only [CollatzResearch.WordTrace]
  refine ⟨152027582378247421658181323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101351721585498281105454215 152027582378247421658181323)
  ·
    refine ⟨228041373567371132487271985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152027582378247421658181323 228041373567371132487271985)
    ·
      refine ⟨171031030175528349365453989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228041373567371132487271985 171031030175528349365453989)
      ·
        refine ⟨32068318157911565506022623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171031030175528349365453989 32068318157911565506022623)
        ·
          refine ⟨48102477236867348259033935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32068318157911565506022623 48102477236867348259033935)
          ·
            refine ⟨72153715855301022388550903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48102477236867348259033935 72153715855301022388550903)
            ·
              refine ⟨108230573782951533582826355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72153715855301022388550903 108230573782951533582826355)
              ·
                refine ⟨162345860674427300374239533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108230573782951533582826355 162345860674427300374239533)
                ·
                  refine ⟨60879697752910237640339825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162345860674427300374239533 60879697752910237640339825)
                  ·
                    refine ⟨45659773314682678230254869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60879697752910237640339825 45659773314682678230254869)
                    ·
                      refine ⟨2140301874125750542043197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45659773314682678230254869 2140301874125750542043197)
                      ·
                        rfl

theorem cell23_4168223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_4168223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168223 prefixEnd_4168223 := by exact prefixLift 4168223
  have htrace : WordTrace (prefixWord ++ tailWord_4168223) baseStart_4168223 baseEnd_4168223 := by
    simpa [prefixWord, tailWord_4168223, baseEnd_4168223] using wordTrace_append hprefix tailTrace_4168223
  have hstable : (prefixWord ++ tailWord_4168223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168223).length < 2 ^ (prefixWord ++ tailWord_4168223).sum := by decide
  have hdescent : baseEnd_4168223 < baseStart_4168223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168264 : List Nat := [2, 1, 3, 1, 1, 1, 1, 8, 1, 1, 3]
def baseStart_4168264 : Nat := 118140960795 + 4168264 * 2 ^ 59
def prefixEnd_4168264 : Nat := 4983230072969 + 3 ^ 40 * 4168264 * 2
def baseEnd_4168264 : Nat := 2140322926832584881630509

theorem tailTrace_4168264 : CollatzResearch.WordTrace tailWord_4168264 prefixEnd_4168264 2140322926832584881630509 := by
  unfold tailWord_4168264
  simp only [CollatzResearch.WordTrace]
  refine ⟨76014538885549442830211923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101352718514065923773615897 76014538885549442830211923)
  ·
    refine ⟨114021808328324164245317885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76014538885549442830211923 114021808328324164245317885)
    ·
      refine ⟨42758178123121561591994207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114021808328324164245317885 42758178123121561591994207)
      ·
        refine ⟨64137267184682342387991311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42758178123121561591994207 64137267184682342387991311)
        ·
          refine ⟨96205900777023513581986967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64137267184682342387991311 96205900777023513581986967)
          ·
            refine ⟨144308851165535270372980451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96205900777023513581986967 144308851165535270372980451)
            ·
              refine ⟨216463276748302905559470677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144308851165535270372980451 216463276748302905559470677)
              ·
                refine ⟨2536679024394174674525047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 216463276748302905559470677 2536679024394174674525047)
                ·
                  refine ⟨3805018536591262011787571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2536679024394174674525047 3805018536591262011787571)
                  ·
                    refine ⟨5707527804886893017681357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3805018536591262011787571 5707527804886893017681357)
                    ·
                      refine ⟨2140322926832584881630509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5707527804886893017681357 2140322926832584881630509)
                      ·
                        rfl

theorem cell23_4168264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_4168264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168264 prefixEnd_4168264 := by exact prefixLift 4168264
  have htrace : WordTrace (prefixWord ++ tailWord_4168264) baseStart_4168264 baseEnd_4168264 := by
    simpa [prefixWord, tailWord_4168264, baseEnd_4168264] using wordTrace_append hprefix tailTrace_4168264
  have hstable : (prefixWord ++ tailWord_4168264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168264).length < 2 ^ (prefixWord ++ tailWord_4168264).sum := by decide
  have hdescent : baseEnd_4168264 < baseStart_4168264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168300 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_4168300 : Nat := 118140960795 + 4168300 * 2 ^ 59
def prefixEnd_4168300 : Nat := 4983230072969 + 3 ^ 40 * 4168300 * 2
def baseEnd_4168300 : Nat := 2140341412136146740780343

theorem tailTrace_4168300 : CollatzResearch.WordTrace tailWord_4168300 prefixEnd_4168300 2140341412136146740780343 := by
  unfold tailWord_4168300
  simp only [CollatzResearch.WordTrace]
  refine ⟨76015195399484231904367177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101353593865978975872489569 76015195399484231904367177)
  ·
    refine ⟨57011396549613173928275383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76015195399484231904367177 57011396549613173928275383)
    ·
      refine ⟨85517094824419760892413075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57011396549613173928275383 85517094824419760892413075)
      ·
        refine ⟨128275642236629641338619613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85517094824419760892413075 128275642236629641338619613)
        ·
          refine ⟨48103365838736115501982355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128275642236629641338619613 48103365838736115501982355)
          ·
            refine ⟨72155048758104173252973533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48103365838736115501982355 72155048758104173252973533)
            ·
              refine ⟨27058143284289064969865075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72155048758104173252973533 27058143284289064969865075)
              ·
                refine ⟨40587214926433597454797613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27058143284289064969865075 40587214926433597454797613)
                ·
                  refine ⟨15220205597412599045549105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40587214926433597454797613 15220205597412599045549105)
                  ·
                    refine ⟨11415154198059449284161829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15220205597412599045549105 11415154198059449284161829)
                    ·
                      refine ⟨2140341412136146740780343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11415154198059449284161829 2140341412136146740780343)
                      ·
                        rfl

theorem cell23_4168300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_4168300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168300 prefixEnd_4168300 := by exact prefixLift 4168300
  have htrace : WordTrace (prefixWord ++ tailWord_4168300) baseStart_4168300 baseEnd_4168300 := by
    simpa [prefixWord, tailWord_4168300, baseEnd_4168300] using wordTrace_append hprefix tailTrace_4168300
  have hstable : (prefixWord ++ tailWord_4168300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168300).length < 2 ^ (prefixWord ++ tailWord_4168300).sum := by decide
  have hdescent : baseEnd_4168300 < baseStart_4168300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4168310 : List Nat := [5, 1, 1, 2, 14]
def baseStart_4168310 : Nat := 118140960795 + 4168310 * 2 ^ 59
def prefixEnd_4168310 : Nat := 4983230072969 + 3 ^ 40 * 4168310 * 2
def baseEnd_4168310 : Nat := 2936003493748548287593

theorem tailTrace_4168310 : CollatzResearch.WordTrace tailWord_4168310 prefixEnd_4168310 2936003493748548287593 := by
  unfold tailWord_4168310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9501922220558264719787399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101353837019288157011065589 9501922220558264719787399)
  ·
    refine ⟨14252883330837397079681099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9501922220558264719787399 14252883330837397079681099)
    ·
      refine ⟨21379324996256095619521649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14252883330837397079681099 21379324996256095619521649)
      ·
        refine ⟨16034493747192071714641237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21379324996256095619521649 16034493747192071714641237)
        ·
          refine ⟨2936003493748548287593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 16034493747192071714641237 2936003493748548287593)
          ·
            rfl

theorem cell23_4168310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 14].length) (baseStart_4168310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4168310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4168310 prefixEnd_4168310 := by exact prefixLift 4168310
  have htrace : WordTrace (prefixWord ++ tailWord_4168310) baseStart_4168310 baseEnd_4168310 := by
    simpa [prefixWord, tailWord_4168310, baseEnd_4168310] using wordTrace_append hprefix tailTrace_4168310
  have hstable : (prefixWord ++ tailWord_4168310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4168310).length < 2 ^ (prefixWord ++ tailWord_4168310).sum := by decide
  have hdescent : baseEnd_4168310 < baseStart_4168310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4168310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
